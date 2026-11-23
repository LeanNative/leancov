import Lean.Data.Json
import LeanCov.Cov

/-! # `leancov` CLI

Subcommands:
- `leancov instrument` — rewrite Lean source trees with source-level coverage probes and write `sites.json`
- `leancov stage`      — stage an entire Lake package into an out-of-tree instrumented build directory
- `leancov run`        — execute a command with `LEAN_COV_FILE` / `LEAN_COV_SITES` initialized
- `leancov report`     — merge `.cov` profiles, print CRAP/Cognitive-CRAP summary, export JSON & LCOV
- `leancov analyze`    — static McCabe CC and Cognitive Complexity report without running tests -/

namespace LeanCov.CLI
open Lean LeanCov.Cov

private def usage : String :=
"leancov — source-level Lean 4 coverage, McCabe CRAP, and Cognitive Complexity

Usage:
  leancov instrument --src <dir>[:<outDir>] [--src ...] [--out <dir>] --sites <sites.json>
                     [--exclude <substr>]... [--imports <Mod1,Mod2>]... [--no-bool-ops]
  leancov stage      --pkg <pkgDir> --out <stageDir> --leancov <leancovDir>
                     [--src-dir <relDir>]... [--sites <sites.json>] [--append-sites]
                     [--prefix <relPrefix>] [--dep <name>=<path>]...
                     [--exclude <substr>]... [--imports <Mod1,Mod2>]... [--no-bool-ops] [--self]
  leancov run        --sites <sites.json> --profile <out.cov> [--append] [--no-defer-init] [--] <cmd> [args...]
  leancov report     --sites <sites.json> (--profile <p.cov> | --profile-dir <dir>)...
                     [--json <out.json>] [--lcov <out.info>] [--top <N>]
                     [--sort crap|cog|cc|uncov] [--files] [--kinds] [--missed]
                     [--min-cov <pct>] [--max-crap <val>] [--max-cog-crap <val>]
  leancov analyze    --src <dir> [--src ...] [--exclude <substr>]... [--imports <Mod1,Mod2>]...
                     [--json <out.json>] [--top <N>] [--sort cog|cc]
"

private def parseFloat? (s : String) : Option Float :=
  let t := s.trimAscii.copy
  match t.splitOn "." with
  | [whole] => whole.toNat?.map Float.ofNat
  | [whole, frac] =>
    match whole.toNat?, frac.toNat? with
    | some w, some f =>
      let denom := Float.pow 10.0 (Float.ofNat frac.length)
      some (Float.ofNat w + Float.ofNat f / denom)
    | _, _ => none
  | _ => none

private def splitImports (s : String) : Array Name :=
  (s.splitOn ",").toArray.filterMap fun p =>
    let t := p.trimAscii.copy
    if t.isEmpty then none else some t.toName

private def readManifest (path : System.FilePath) : IO Manifest := do
  let raw ← IO.FS.readFile path
  match Json.parse raw >>= fromJson? with
  | .ok m => return m
  | .error e => throw (IO.userError s!"{path}: invalid manifest JSON: {e}")

private def writeManifest (path : System.FilePath) (m : Manifest) : IO Unit := do
  if let some p := path.parent then IO.FS.createDirAll p
  IO.FS.writeFile path (toJson m).pretty

private def canonicalOrAbs (p : System.FilePath) : IO System.FilePath := do
  try
    IO.FS.realPath p
  catch _ =>
    if p.isAbsolute then return p
    else return (← IO.currentDir) / p

private def splitColonPair (s : String) : String × Option String :=
  match s.splitOn ":" with
  | [a, b] => (a, some b)
  | _ => (s, none)

private def isPrefixPath (root child : System.FilePath) : Bool :=
  let r := root.toString
  let c := child.toString
  let rp := if r.endsWith "/" then r else r ++ "/"
  c == r || c.startsWith rp

/-- Create a symbolic link `linkPath -> target`, replacing any existing entry at `linkPath`. -/
private def forceSymlink (target linkPath : System.FilePath) : IO Unit := do
  if let some p := linkPath.parent then IO.FS.createDirAll p
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", linkPath.toString] }
  let res ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, linkPath.toString] }
  if res.exitCode != 0 then
    throw (IO.userError s!"ln -s {target} {linkPath} failed: {res.stderr}")

/-- Run `leancov instrument`. -/
private unsafe def cmdInstrument (args : List String) : IO UInt32 := do
  let mut srcs : Array (System.FilePath × Option System.FilePath) := #[]
  let mut outDir : Option System.FilePath := none
  let mut sitesPath : Option System.FilePath := none
  let mut excludes : Array String := #[]
  let mut extraImports : Array Name := #[]
  let mut boolOps : Bool := true
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--src" :: v :: tl =>
      let (a, b) := splitColonPair v
      srcs := srcs.push (⟨a⟩, b.map System.FilePath.mk)
      rest := tl
    | "--out" :: v :: tl => outDir := some ⟨v⟩; rest := tl
    | "--sites" :: v :: tl => sitesPath := some ⟨v⟩; rest := tl
    | "--exclude" :: v :: tl => excludes := excludes.push v; rest := tl
    | "--imports" :: v :: tl => extraImports := extraImports ++ splitImports v; rest := tl
    | "--no-bool-ops" :: tl => boolOps := false; rest := tl
    | flag :: _ =>
      IO.eprintln s!"unknown option for instrument: {flag}"
      return 2
    | [] => break
  if srcs.isEmpty then
    IO.eprintln "instrument: at least one --src <dir> is required"
    return 2
  let some sitesOut := sitesPath | do
    IO.eprintln "instrument: --sites <sites.json> is required"
    return 2
  let cfg : InstrumentConfig := {
    exclude := excludes
    extraImports := extraImports
    instrumentBoolOps := boolOps
  }
  let mut nextId : Nat := 0
  let mut allSites : Array Site := #[]
  let mut allFuncs : Array FuncInfo := #[]
  let mut allSkipped : Array (String × String) := #[]
  for (srcDir, explicitOut) in srcs do
    let relPrefix := srcDir.fileName.getD ""
    let targetOut ← match explicitOut, outDir with
      | some d, _ => pure d
      | none, some d => pure (if srcs.size > 1 then d / relPrefix else d)
      | none, none =>
        IO.eprintln "instrument: --out <dir> (or --src <src>:<out>) is required"
        return 2
    let m ← instrumentTree srcDir targetOut cfg nextId (if srcs.size > 1 then relPrefix else "")
    nextId := nextId + m.sites.size
    allSites := allSites ++ m.sites
    allFuncs := allFuncs ++ m.functions
    allSkipped := allSkipped ++ m.skippedFiles
  let manifest : Manifest := { version := 1, sites := allSites, functions := allFuncs, skippedFiles := allSkipped }
  writeManifest sitesOut manifest
  IO.println s!"Instrumented {allFuncs.size} declarations ({allSites.size} probe sites) -> {sitesOut}"
  if !allSkipped.isEmpty then
    IO.eprintln s!"Warning: {allSkipped.size} file(s) skipped:"
    for (f, why) in allSkipped do
      IO.eprintln s!"  {f}: {why}"
  return 0

private def parseDepOverride (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | [k, v] => if k.isEmpty || v.isEmpty then none else some (k, v)
  | _ => none

private def lookupDep (deps : Array (String × String)) (name : String) : Option String :=
  (deps.find? (·.1 == name)).map (·.2)

/-- Rewrite relative `from "..."` paths in `lakefile.lean` to absolute paths and optionally require `leancov`. -/
private def rewriteLakefileLean (content : String) (pkgAbs leancovAbs : System.FilePath) (isSelf : Bool)
    (depOverrides : Array (String × String) := #[]) : String := Id.run do
  let lines := content.splitOn "\n"
  let mut out : Array String := #[]
  let mut alreadyHasLeancov := false
  for line in lines do
    let trimmed := line.trimAscii.copy
    if trimmed.startsWith "require " && (trimmed.splitOn "leancov").length > 1 then
      alreadyHasLeancov := true
    if trimmed.startsWith "require " then
      match line.splitOn " from \"" with
      | [lhs, rhs] =>
        let depName := (lhs.trimAscii.copy.drop 8).toString.trimAscii.copy
        match rhs.splitOn "\"" with
        | rel :: tail =>
          if let some ov := lookupDep depOverrides depName then
            out := out.push (lhs ++ " from \"" ++ ov ++ "\"" ++ "\"".intercalate tail)
          else if !rel.startsWith "/" && !rel.startsWith "http://" && !rel.startsWith "https://" && !rel.startsWith "git@" then
            let abs := (pkgAbs / rel).toString
            out := out.push (lhs ++ " from \"" ++ abs ++ "\"" ++ "\"".intercalate tail)
          else
            out := out.push line
        | _ => out := out.push line
      | _ => out := out.push line
    else
      out := out.push line
  if !isSelf && !alreadyHasLeancov then
    out := out.push ""
    out := out.push s!"require leancov from \"{leancovAbs}\""
  return "\n".intercalate out.toList

/-- Rewrite relative `path = "..."` in `lakefile.toml` to absolute paths and optionally require `leancov`. -/
private def rewriteLakefileToml (content : String) (pkgAbs leancovAbs : System.FilePath) (isSelf : Bool)
    (depOverrides : Array (String × String) := #[]) : String := Id.run do
  let lines := content.splitOn "\n"
  let mut out : Array String := #[]
  let mut inRequire := false
  let mut curDepName : String := ""
  let mut alreadyHasLeancov := false
  for line in lines do
    let t := line.trimAscii.copy
    if t.startsWith "[[" || t.startsWith "[" then
      inRequire := t == "[[require]]"
      curDepName := ""
    if inRequire && t.startsWith "name" then
      match t.splitOn "\"" with
      | [_, nm, _] =>
        curDepName := nm
        if nm == "leancov" then alreadyHasLeancov := true
      | _ => pure ()
    if inRequire && t.startsWith "path" then
      match line.splitOn "\"" with
      | [pre, rel, post] =>
        if let some ov := lookupDep depOverrides curDepName then
          out := out.push (pre ++ "\"" ++ ov ++ "\"" ++ post)
        else if !rel.startsWith "/" then
          out := out.push (pre ++ "\"" ++ (pkgAbs / rel).toString ++ "\"" ++ post)
        else
          out := out.push line
      | _ => out := out.push line
    else
      out := out.push line
  if !isSelf && !alreadyHasLeancov then
    out := out.push ""
    out := out.push "[[require]]"
    out := out.push "name = \"leancov\""
    out := out.push s!"path = \"{leancovAbs}\""
  return "\n".intercalate out.toList

/-- Copy `lake-manifest.json` into the staged repo, absolutizing local path deps and adding `leancov`. -/
private def stageLakeManifest (pkgAbs stageAbs leancovAbs : System.FilePath) (isSelf : Bool)
    (depOverrides : Array (String × String) := #[]) : IO Unit := do
  let srcManifest := pkgAbs / "lake-manifest.json"
  if !(← srcManifest.pathExists) then return
  let raw ← IO.FS.readFile srcManifest
  match Json.parse raw with
  | .error _ =>
    IO.FS.writeFile (stageAbs / "lake-manifest.json") raw
  | .ok j =>
    let pkgsJson := match j.getObjVal? "packages" with
      | .ok (.arr arr) => arr
      | _ => #[]
    let mut updated : Array Json := #[]
    let mut hasLeancov := false
    for p in pkgsJson do
      let name := (p.getObjValAs? String "name").toOption.getD ""
      if name == "leancov" then hasLeancov := true
      let p' := match p.getObjValAs? String "type", p.getObjValAs? String "dir" with
        | .ok "path", .ok dir =>
          let newDir := match lookupDep depOverrides name with
            | some ov => ov
            | none => if dir.startsWith "/" then dir else (pkgAbs / dir).toString
          match p with
          | .obj kvs => Json.obj (kvs.insert "dir" (Json.str newDir))
          | other => other
        | _, _ => p
      updated := updated.push p'
    if !isSelf && !hasLeancov then
      let entry := Json.mkObj [
        ("type", Json.str "path"),
        ("scope", Json.str ""),
        ("name", Json.str "leancov"),
        ("manifestFile", Json.str "lake-manifest.json"),
        ("inherited", Json.bool false),
        ("dir", Json.str leancovAbs.toString),
        ("copy", Json.bool false),
        ("configFile", Json.str "lakefile.lean")
      ]
      updated := updated.push entry
    let outJson := match j with
      | .obj kvs => Json.obj (kvs.insert "packages" (Json.arr updated))
      | other => other
    IO.FS.writeFile (stageAbs / "lake-manifest.json") outJson.pretty

private def dirContainsLean (dir : System.FilePath) : IO Bool := do
  let fs ← collectLeanFiles dir
  return !fs.isEmpty

private def dirHasMainLean (dir : System.FilePath) : IO Bool := do
  for f in (← collectLeanFiles dir) do
    let txt ← IO.FS.readFile f
    if (txt.splitOn "main").length > 1 then return true
  return false

private partial def copyDirArmingMains (env : Environment) (srcDir dstDir : System.FilePath) : IO Bool := do
  IO.FS.createDirAll dstDir
  let mut armedAny := false
  for entry in (← srcDir.readDir) do
    let name := entry.fileName
    if name == ".git" || name == ".lake" || name == "build" then continue
    let sp := entry.path
    let dp := dstDir / name
    if ← sp.isDir then
      let a ← copyDirArmingMains env sp dp
      if a then armedAny := true
    else if sp.extension == some "lean" then
      let src ← IO.FS.readFile sp
      let (outSrc, armed) ← armMainInSource env sp.toString src
      if armed then armedAny := true
      IO.FS.writeFile dp outSrc
    else
      IO.FS.writeBinFile dp (← IO.FS.readBinFile sp)
  return armedAny

/-- Run `leancov stage`: create a clean out-of-tree instrumented copy of any Lake package. -/
private unsafe def cmdStage (args : List String) : IO UInt32 := do
  let mut pkgDir : System.FilePath := "."
  let mut stageDir : Option System.FilePath := none
  let mut leancovDir : Option System.FilePath := none
  let mut srcDirs : Array String := #[]
  let mut sitesPath : Option System.FilePath := none
  let mut appendSites : Bool := false
  let mut pathPrefix : String := ""
  let mut depOverrides : Array (String × String) := #[]
  let mut excludes : Array String := #[]
  let mut extraImports : Array Name := #[]
  let mut boolOps : Bool := true
  let mut isSelf : Bool := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--pkg" :: v :: tl => pkgDir := ⟨v⟩; rest := tl
    | "--out" :: v :: tl => stageDir := some ⟨v⟩; rest := tl
    | "--leancov" :: v :: tl => leancovDir := some ⟨v⟩; rest := tl
    | "--src-dir" :: v :: tl => srcDirs := srcDirs.push v; rest := tl
    | "--sites" :: v :: tl => sitesPath := some ⟨v⟩; rest := tl
    | "--append-sites" :: tl => appendSites := true; rest := tl
    | "--prefix" :: v :: tl => pathPrefix := v; rest := tl
    | "--dep" :: v :: tl =>
      match parseDepOverride v with
      | some (k, p) =>
        let abs ← canonicalOrAbs ⟨p⟩
        depOverrides := depOverrides.push (k, abs.toString)
        rest := tl
      | none => IO.eprintln s!"invalid --dep value (expected name=path): {v}"; return 2
    | "--exclude" :: v :: tl => excludes := excludes.push v; rest := tl
    | "--imports" :: v :: tl => extraImports := extraImports ++ splitImports v; rest := tl
    | "--no-bool-ops" :: tl => boolOps := false; rest := tl
    | "--self" :: tl => isSelf := true; rest := tl
    | flag :: _ =>
      IO.eprintln s!"unknown option for stage: {flag}"
      return 2
    | [] => break
  let some outDir := stageDir | do
    IO.eprintln "stage: --out <stageDir> is required"
    return 2
  let pkgAbs ← canonicalOrAbs pkgDir
  IO.FS.createDirAll outDir
  let stageAbs ← canonicalOrAbs outDir
  let leancovAbs ← match leancovDir with
    | some d => canonicalOrAbs d
    | none =>
      if isSelf then pure pkgAbs
      else do
        IO.eprintln "stage: --leancov <leancovDir> is required (or pass --self)"
        return 2
  if !isSelf && pkgAbs == leancovAbs then
    isSelf := true

  let sitesOut := sitesPath.getD (stageAbs / "sites.json")
  let cfg : InstrumentConfig := {
    exclude := excludes
    extraImports := extraImports
    instrumentBoolOps := boolOps
  }

  -- Auto-discover source directories if none were given explicitly
  let mut toInstrument : Array String := srcDirs
  if toInstrument.isEmpty then
    for entry in (← pkgAbs.readDir) do
      let name := entry.fileName
      if name == ".git" || name == ".lake" || name == "build" || name.startsWith "." then continue
      let p := entry.path
      if isPrefixPath p stageAbs then continue
      if (← p.isDir) && (← dirContainsLean p) then
        toInstrument := toInstrument.push name
    toInstrument := toInstrument.qsort (· < ·)

  let env ← loadParserEnv cfg.extraImports
  let mut armedAny : Bool := false

  -- Stage non-source top-level entries
  for entry in (← pkgAbs.readDir) do
    let name := entry.fileName
    if name == ".git" || name == ".lake" || name == "build" then continue
    let srcPath := entry.path
    if isPrefixPath srcPath stageAbs then continue
    let dstPath := stageAbs / name
    if name == "lakefile.lean" then
      let txt ← IO.FS.readFile srcPath
      IO.FS.writeFile dstPath (rewriteLakefileLean txt pkgAbs leancovAbs isSelf depOverrides)
    else if name == "lakefile.toml" then
      let txt ← IO.FS.readFile srcPath
      IO.FS.writeFile dstPath (rewriteLakefileToml txt pkgAbs leancovAbs isSelf depOverrides)
    else if name == "lake-manifest.json" then
      stageLakeManifest pkgAbs stageAbs leancovAbs isSelf depOverrides
    else if toInstrument.contains name then
      -- Will be instrumented below
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dstPath.toString] }
    else if ← srcPath.isDir then
      if ← dirHasMainLean srcPath then
        let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dstPath.toString] }
        let a ← copyDirArmingMains env srcPath dstPath
        if a then armedAny := true
      else
        forceSymlink srcPath dstPath
    else if srcPath.extension == some "lean" then
      -- Top-level `.lean` file (e.g. `Main.lean`): instrument/arm directly below
      pure ()
    else
      let bytes ← IO.FS.readBinFile srcPath
      IO.FS.writeBinFile dstPath bytes

  -- Symlink existing `.lake/packages/*` individually so offline builds reuse them without modifying pkgAbs
  let pkgDepsDir := pkgAbs / ".lake" / "packages"
  if ← pkgDepsDir.isDir then
    let stageDepsDir := stageAbs / ".lake" / "packages"
    IO.FS.createDirAll stageDepsDir
    for entry in (← pkgDepsDir.readDir) do
      forceSymlink entry.path (stageDepsDir / entry.fileName)

  -- Instrument source directories and top-level `.lean` files
  let mut nextId : Nat := 0
  let mut allSites : Array Site := #[]
  let mut allFuncs : Array FuncInfo := #[]
  let mut allSkipped : Array (String × String) := #[]
  if appendSites && (← sitesOut.pathExists) then
    let prev ← readManifest sitesOut
    nextId := prev.sites.size
    allSites := prev.sites
    allFuncs := prev.functions
    allSkipped := prev.skippedFiles
    if prev.armOnMain then armedAny := true

  for dirName in toInstrument do
    let dispPfx := if pathPrefix.isEmpty then dirName else s!"{pathPrefix}/{dirName}"
    let m ← instrumentTree (pkgAbs / dirName) (stageAbs / dirName) cfg nextId dispPfx (armMains := true)
    nextId := nextId + m.sites.size
    allSites := allSites ++ m.sites
    allFuncs := allFuncs ++ m.functions
    allSkipped := allSkipped ++ m.skippedFiles
    if m.armOnMain then armedAny := true

  -- Instrument any top-level `.lean` files (excluding `lakefile.lean`), arming `def main` even when excluded
  for entry in (← pkgAbs.readDir) do
    let name := entry.fileName
    if name == "lakefile.lean" then continue
    let p := entry.path
    if !(← p.isDir) && p.extension == some "lean" then
      let src ← IO.FS.readFile p
      let dispName := if pathPrefix.isEmpty then name else s!"{pathPrefix}/{name}"
      let excl := cfg.exclude.any fun pat => !pat.isEmpty && ((name.splitOn pat).length > 1 || (dispName.splitOn pat).length > 1)
      if excl then
        let (outSrc, armed) ← armMainInSource env dispName src
        if armed then armedAny := true
        IO.FS.writeFile (stageAbs / name) outSrc
      else
        let res ← instrumentSource env dispName src nextId cfg
        nextId := res.nextSiteId
        allSites := allSites ++ res.sites
        allFuncs := allFuncs ++ res.functions
        if let some why := res.skippedReason then
          allSkipped := allSkipped.push (dispName, why)
        let (outSrc, armed) ← armMainInSource env dispName res.instrumented
        if armed then armedAny := true
        IO.FS.writeFile (stageAbs / name) outSrc

  let manifest : Manifest := {
    version := 1, armOnMain := armedAny, sites := allSites, functions := allFuncs, skippedFiles := allSkipped
  }
  writeManifest sitesOut manifest
  IO.println s!"Staged {pkgAbs} -> {stageAbs}"
  IO.println s!"  Instrumented dirs: {", ".intercalate toInstrument.toList}"
  IO.println s!"  Declarations: {allFuncs.size} | Probe sites: {allSites.size} | Manifest: {sitesOut}"
  if !allSkipped.isEmpty then
    IO.eprintln s!"  Warning: {allSkipped.size} file(s) skipped:"
    for (f, why) in allSkipped do
      IO.eprintln s!"    {f}: {why}"
  return 0

/-- Run `leancov run`: pre-initialize `.cov` profile and run target executable with env vars set. -/
private def cmdRun (args : List String) : IO UInt32 := do
  let mut sitesPath : Option System.FilePath := none
  let mut profilePath : Option System.FilePath := none
  let mut appendMode : Bool := false
  let mut noDeferInit : Bool := false
  let mut cmdArgs : List String := []
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--sites" :: v :: tl => sitesPath := some ⟨v⟩; rest := tl
    | "--profile" :: v :: tl => profilePath := some ⟨v⟩; rest := tl
    | "--append" :: tl => appendMode := true; rest := tl
    | "--no-defer-init" :: tl => noDeferInit := true; rest := tl
    | "--" :: tl => cmdArgs := tl; break
    | tok :: tl =>
      if tok.startsWith "--" then
        IO.eprintln s!"unknown option for run: {tok}"
        return 2
      else
        cmdArgs := tok :: tl; break
    | [] => break
  let some sp := sitesPath | do IO.eprintln "run: --sites <sites.json> is required"; return 2
  let some pp := profilePath | do IO.eprintln "run: --profile <out.cov> is required"; return 2
  let cmd :: cargs := cmdArgs | do IO.eprintln "run: command to execute is required"; return 2
  let m ← readManifest sp
  let siteCount := m.sites.size
  let profAbs ← canonicalOrAbs pp
  let hasPidPlaceholder := (profAbs.toString.splitOn "%p").length > 1
  if !hasPidPlaceholder then
    if !(appendMode && (← profAbs.pathExists)) then
      initProfile profAbs siteCount
  else if let some parent := profAbs.parent then
    IO.FS.createDirAll parent
  let mut envVars : Array (String × Option String) := #[
    ("LEAN_COV_FILE", some profAbs.toString),
    ("LEAN_COV_SITES", some (toString siteCount))
  ]
  if m.armOnMain && !noDeferInit then
    envVars := envVars.push ("LEAN_COV_DEFER_INIT", some "1")
  let child ← IO.Process.spawn {
    cmd := cmd
    args := cargs.toArray
    env := envVars
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  child.wait

/-- Collect all `.cov` files inside a directory. -/
private def collectCovFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  if !(← dir.isDir) then return out
  for entry in (← dir.readDir) do
    let p := entry.path
    if !(← p.isDir) && p.extension == some "cov" then
      out := out.push p
  return out.qsort fun a b => a.toString < b.toString

/-- Run `leancov report`. -/
private def cmdReport (args : List String) : IO UInt32 := do
  let mut sitesPath : Option System.FilePath := none
  let mut profiles : Array System.FilePath := #[]
  let mut jsonOut : Option System.FilePath := none
  let mut lcovOut : Option System.FilePath := none
  let mut topN : Nat := 25
  let mut sortBy : SortKey := .crap
  let mut showFiles : Bool := false
  let mut showKinds : Bool := false
  let mut showMissed : Bool := false
  let mut minCov : Option Float := none
  let mut maxCrap : Option Float := none
  let mut maxCogCrap : Option Float := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--sites" :: v :: tl => sitesPath := some ⟨v⟩; rest := tl
    | "--profile" :: v :: tl => profiles := profiles.push ⟨v⟩; rest := tl
    | "--profile-dir" :: v :: tl =>
      profiles := profiles ++ (← collectCovFiles ⟨v⟩); rest := tl
    | "--json" :: v :: tl => jsonOut := some ⟨v⟩; rest := tl
    | "--lcov" :: v :: tl => lcovOut := some ⟨v⟩; rest := tl
    | "--top" :: v :: tl =>
      match v.toNat? with
      | some n => topN := n; rest := tl
      | none => IO.eprintln s!"invalid --top value: {v}"; return 2
    | "--sort" :: v :: tl =>
      match SortKey.ofString? v with
      | some k => sortBy := k; rest := tl
      | none => IO.eprintln s!"invalid --sort value: {v} (use crap|cog|cc|uncov)"; return 2
    | "--files" :: tl => showFiles := true; rest := tl
    | "--kinds" :: tl => showKinds := true; rest := tl
    | "--missed" :: tl => showMissed := true; rest := tl
    | "--min-cov" :: v :: tl =>
      match parseFloat? v with
      | some f => minCov := some f; rest := tl
      | none => IO.eprintln s!"invalid --min-cov value: {v}"; return 2
    | "--max-crap" :: v :: tl =>
      match parseFloat? v with
      | some f => maxCrap := some f; rest := tl
      | none => IO.eprintln s!"invalid --max-crap value: {v}"; return 2
    | "--max-cog-crap" :: v :: tl =>
      match parseFloat? v with
      | some f => maxCogCrap := some f; rest := tl
      | none => IO.eprintln s!"invalid --max-cog-crap value: {v}"; return 2
    | flag :: _ =>
      IO.eprintln s!"unknown option for report: {flag}"
      return 2
    | [] => break
  let some sp := sitesPath | do IO.eprintln "report: --sites <sites.json> is required"; return 2
  if profiles.isEmpty then
    IO.eprintln "report: at least one --profile <file.cov> or --profile-dir <dir> is required"
    return 2
  let m ← readManifest sp
  let hits ← mergeProfiles profiles m.sites.size
  let rep := buildReport m hits
  IO.println (formatReport rep topN sortBy showFiles showMissed showKinds)
  if let some jp := jsonOut then
    if let some p := jp.parent then IO.FS.createDirAll p
    IO.FS.writeFile jp (toJson rep).pretty
  if let some lp := lcovOut then
    if let some p := lp.parent then IO.FS.createDirAll p
    IO.FS.writeFile lp (toLcov m hits)

  let mut failed := false
  if let some mc := minCov then
    let pct := rep.branchCov * 100.0
    if pct < mc then
      IO.eprintln s!"FAIL: branch coverage {pct}% < --min-cov {mc}%"
      failed := true
  if let some xc := maxCrap then
    if rep.maxCrap > xc then
      IO.eprintln s!"FAIL: max McCabe CRAP {rep.maxCrap} > --max-crap {xc}"
      failed := true
  if let some xg := maxCogCrap then
    if rep.maxCogCrap > xg then
      IO.eprintln s!"FAIL: max Cognitive CRAP {rep.maxCogCrap} > --max-cog-crap {xg}"
      failed := true
  return if failed then 1 else 0

/-- Run `leancov analyze`: static CC and Cognitive Complexity without building or running tests. -/
private unsafe def cmdAnalyze (args : List String) : IO UInt32 := do
  let mut srcs : Array System.FilePath := #[]
  let mut excludes : Array String := #[]
  let mut extraImports : Array Name := #[]
  let mut jsonOut : Option System.FilePath := none
  let mut topN : Nat := 30
  let mut sortByCog : Bool := true
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--src" :: v :: tl => srcs := srcs.push ⟨v⟩; rest := tl
    | "--exclude" :: v :: tl => excludes := excludes.push v; rest := tl
    | "--imports" :: v :: tl => extraImports := extraImports ++ splitImports v; rest := tl
    | "--json" :: v :: tl => jsonOut := some ⟨v⟩; rest := tl
    | "--top" :: v :: tl =>
      match v.toNat? with
      | some n => topN := n; rest := tl
      | none => IO.eprintln s!"invalid --top value: {v}"; return 2
    | "--sort" :: "cc" :: tl => sortByCog := false; rest := tl
    | "--sort" :: "cog" :: tl => sortByCog := true; rest := tl
    | flag :: _ =>
      IO.eprintln s!"unknown option for analyze: {flag}"
      return 2
    | [] => break
  if srcs.isEmpty then
    IO.eprintln "analyze: at least one --src <dir> is required"
    return 2
  let cfg : InstrumentConfig := {
    exclude := excludes
    extraImports := extraImports
    analyzeOnly := true
  }
  let mut nextId : Nat := 0
  let mut allSites : Array Site := #[]
  let mut allFuncs : Array FuncInfo := #[]
  let mut allSkipped : Array (String × String) := #[]
  for srcDir in srcs do
    let relPrefix := if srcs.size > 1 then srcDir.fileName.getD "" else ""
    let m ← instrumentTree srcDir srcDir cfg nextId relPrefix
    nextId := nextId + m.sites.size
    allSites := allSites ++ m.sites
    allFuncs := allFuncs ++ m.functions
    allSkipped := allSkipped ++ m.skippedFiles
  let manifest : Manifest := { version := 1, sites := allSites, functions := allFuncs, skippedFiles := allSkipped }
  IO.println (formatStaticAnalysis manifest topN sortByCog)
  if let some jp := jsonOut then
    if let some p := jp.parent then IO.FS.createDirAll p
    IO.FS.writeFile jp (toJson manifest).pretty
  return 0

unsafe def runCLI (args : List String) : IO UInt32 := do
  match args with
  | "instrument" :: rest => cmdInstrument rest
  | "stage" :: rest => cmdStage rest
  | "run" :: rest => cmdRun rest
  | "report" :: rest => cmdReport rest
  | "analyze" :: rest => cmdAnalyze rest
  | "--help" :: _ | "-h" :: _ | "help" :: _ | [] =>
    IO.println usage
    return 0
  | cmd :: _ =>
    IO.eprintln s!"unknown subcommand: {cmd}\n\n{usage}"
    return 2

end LeanCov.CLI
