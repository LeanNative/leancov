import Lean.Data.Json
import Std.Data.HashMap
import Std.Sync.Mutex
import LeanCov.Runtime
import LeanCov.Cov

/-! # `leancov` CLI

Subcommands:
- `leancov instrument` — rewrite Lean source trees with source-level coverage probes and write `sites.json`
- `leancov stage`      — stage an entire Lake package into an out-of-tree instrumented build directory
- `leancov run`        — execute a command with `LEAN_COV_FILE` / `LEAN_COV_SITES` initialized
- `leancov merge`      — combine multiple `.cov` profiles into one merged `.cov` file
- `leancov report`     — merge `.cov` profiles, print CRAP/Cognitive-CRAP/patch/hot summary, export HTML/JSON/LCOV/Markdown
- `leancov test`       — declarative multi-package test & coverage runner configured by `leancov.toml`
- `leancov diff`       — compare two JSON coverage reports for CI regression gating
- `leancov analyze`    — static McCabe CC and Cognitive Complexity report without running tests
- `leancov mutate`     — AST-guided, coverage-pruned, proof-aware mutation testing in isolated workspaces -/

namespace LeanCov.CLI
open Lean LeanCov.Cov

/-- Package version printed by `leancov --version` / `-V`. -/
def version : String := "0.4.0"

private def usage : String :=
"leancov — source-level Lean 4 coverage, McCabe CRAP, Cognitive Complexity, and AST Mutation Testing

Usage:
  leancov instrument --src <dir>[:<outDir>] [--src ...] [--out <dir>] --sites <sites.json>
                     [--exclude <substr>]... [--imports <Mod1,Mod2>]... [--no-bool-ops] [--include-cafs]
  leancov stage      --pkg <pkgDir> --out <stageDir> [--leancov <leancovDir>]
                     [--src-dir <relDir>]... [--sites <sites.json>] [--append-sites]
                     [--prefix <relPrefix>] [--dep <name>=<path>]...
                     [--exclude <substr>]... [--imports <Mod1,Mod2>]... [--no-bool-ops] [--include-cafs] [--self]
  leancov run        --sites <sites.json> --profile <out.cov> [--append] [--no-defer-init] [--] <cmd> [args...]
  leancov merge      --out <merged.cov> (--profile <p.cov> | --profile-dir <dir>)...
  leancov report     --sites <sites.json> (--profile <p.cov> | --profile-dir <dir>)...
                     [--json <out.json>] [--lcov <out.info>] [--markdown <out.md>] [--html <dir>] [--top <N>]
                     [--sort crap|cog|cc|uncov|cov] [--file <substr>]... [--decl <substr>]...
                     [--exclude-kind <kind>]... [--exclude-instances] [--files] [--kinds] [--missed]
                     [--missed-detail] [--src-root <dir>] [--hot]
                     [--git-diff <baseRef>] [--repo <dir>] [--min-patch-cov <pct>]
                     [--min-cov <pct>] [--max-crap <val>] [--max-cog-crap <val>]
  leancov test       [--config <leancov.toml>] [--leancov <leancovDir>] [--fast] [--clean]
                     [--no-build] [--report] [--list] [--jobs <N>]
                     [--sort crap|cog|cc|uncov|cov] [--top <N>]
                     [--html <dir>] [--markdown <out.md>] [--exclude-instances]
                     [--min-cov <pct>] [--max-crap <val>] [--max-cog-crap <val>] [suite ...]
  leancov diff       --base <old.json> --head <new.json> [--top <N>]
                     [--json <out.json>] [--markdown <out.md>]
                     [--max-cov-drop <pct>] [--max-crap-delta <val>]
  leancov analyze    --src <dir> [--src ...] [--exclude <substr>]... [--imports <Mod1,Mod2>]...
                     [--json <out.json>] [--top <N>] [--sort cog|cc]
  leancov mutate     --pkg <pkgDir> [--out <workDir>] (--file <relFile> | --src-dir <relDir>)...
                     [--filter <declSubstr>]... [--kinds <k1,k2>]... [--jobs <N>]
                     [--max-mutants <N>] [--seed <N>] [--timeout <sec>]
                     [--build-target <lakeTarget>]... [--proof-target <lakeTarget>]... [--no-build]
                     [--sites <sites.json> (--profile <p.cov> | --profile-dir <dir>)...]
                     [--git-diff <baseRef>] [--no-arith] [--include-interp] [--imports <Mod1,Mod2>]...
                     [--json <out.json>] [--markdown <out.md>] [--min-score <pct>] [--keep-work] -- <testCmd> [args...]
  leancov --version | -V
  leancov --help | -h
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

private def splitCommaNonEmpty (s : String) : Array String :=
  (s.splitOn ",").toArray.filterMap fun p =>
    let t := p.trimAscii.copy
    if t.isEmpty then none else some t

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
  let mut includeCafs : Bool := false
  let mut rest := args
  repeat
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
    | "--include-cafs" :: tl => includeCafs := true; rest := tl
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
    includeCafs := includeCafs
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
    out := out.push ""
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
    out := out.push ""
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
    if isIgnoredDirName name then continue
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

private structure StageOpts where
  pkgDir : System.FilePath := "."
  stageDir : Option System.FilePath := none
  leancovDir : Option System.FilePath := none
  srcDirs : Array String := #[]
  sitesPath : Option System.FilePath := none
  appendSites : Bool := false
  pathPrefix : String := ""
  depOverrides : Array (String × String) := #[]
  excludes : Array String := #[]
  extraImports : Array Name := #[]
  boolOps : Bool := true
  includeCafs : Bool := false
  isSelf : Bool := false
  deriving Inhabited

private def parseStageArgs : List String → StageOpts → Except String StageOpts
  | [], o => pure o
  | "--pkg" :: v :: tl, o => parseStageArgs tl { o with pkgDir := ⟨v⟩ }
  | "--out" :: v :: tl, o => parseStageArgs tl { o with stageDir := some ⟨v⟩ }
  | "--leancov" :: v :: tl, o => parseStageArgs tl { o with leancovDir := some ⟨v⟩ }
  | "--src-dir" :: v :: tl, o => parseStageArgs tl { o with srcDirs := o.srcDirs.push v }
  | "--sites" :: v :: tl, o => parseStageArgs tl { o with sitesPath := some ⟨v⟩ }
  | "--append-sites" :: tl, o => parseStageArgs tl { o with appendSites := true }
  | "--prefix" :: v :: tl, o => parseStageArgs tl { o with pathPrefix := v }
  | "--dep" :: v :: tl, o =>
    match parseDepOverride v with
    | some pair => parseStageArgs tl { o with depOverrides := o.depOverrides.push pair }
    | none => throw s!"invalid --dep value (expected name=path): {v}"
  | "--exclude" :: v :: tl, o => parseStageArgs tl { o with excludes := o.excludes.push v }
  | "--imports" :: v :: tl, o => parseStageArgs tl { o with extraImports := o.extraImports ++ splitImports v }
  | "--no-bool-ops" :: tl, o => parseStageArgs tl { o with boolOps := false }
  | "--include-cafs" :: tl, o => parseStageArgs tl { o with includeCafs := true }
  | "--self" :: tl, o => parseStageArgs tl { o with isSelf := true }
  | flag :: _, _ => throw s!"unknown option for stage: {flag}"

private def resolveLeancovDir (pkgAbs : System.FilePath) (opts : StageOpts) :
    IO (Except String (System.FilePath × Bool)) := do
  match opts.leancovDir with
  | some d =>
    let abs ← canonicalOrAbs d
    return .ok (abs, opts.isSelf || pkgAbs == abs)
  | none =>
    if opts.isSelf then return .ok (pkgAbs, true)
    let mut dir? := (← IO.appPath).parent
    for _ in [:8] do
      let some d := dir? | break
      if (← (d / "lakefile.lean").pathExists) && (← (d / "LeanCov" / "Runtime.lean").pathExists) then
        let abs ← canonicalOrAbs d
        return .ok (abs, pkgAbs == abs)
      dir? := d.parent
    return .error "stage: --leancov <leancovDir> is required (or pass --self)"

private def discoverStageSrcDirs (pkgAbs stageAbs : System.FilePath) (explicit : Array String) :
    IO (Array String) := do
  if !explicit.isEmpty then return explicit
  let mut dirs : Array String := #[]
  for entry in (← pkgAbs.readDir) do
    let name := entry.fileName
    if isIgnoredDirName name || name.startsWith "." then continue
    let p := entry.path
    if isPrefixPath p stageAbs then continue
    if (← p.isDir) && (← dirContainsLean p) then
      dirs := dirs.push name
  return dirs.qsort (· < ·)

private def stageTopLevelEntry (env : Environment) (pkgAbs stageAbs leancovAbs : System.FilePath)
    (isSelf : Bool) (depOverrides : Array (String × String)) (toInstrument : Array String)
    (entry : IO.FS.DirEntry) : IO Bool := do
  let name := entry.fileName
  if isIgnoredDirName name then return false
  let srcPath := entry.path
  if isPrefixPath srcPath stageAbs then return false
  let dstPath := stageAbs / name
  if name == "lakefile.lean" then
    let txt ← IO.FS.readFile srcPath
    IO.FS.writeFile dstPath (rewriteLakefileLean txt pkgAbs leancovAbs isSelf depOverrides)
    return false
  else if name == "lakefile.toml" then
    let txt ← IO.FS.readFile srcPath
    IO.FS.writeFile dstPath (rewriteLakefileToml txt pkgAbs leancovAbs isSelf depOverrides)
    return false
  else if name == "lake-manifest.json" then
    stageLakeManifest pkgAbs stageAbs leancovAbs isSelf depOverrides
    return false
  else if toInstrument.contains name then
    -- Will be instrumented below
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dstPath.toString] }
    return false
  else if ← srcPath.isDir then
    if ← dirHasMainLean srcPath then
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dstPath.toString] }
      return ← copyDirArmingMains env srcPath dstPath
    else
      forceSymlink srcPath dstPath
      return false
  else if srcPath.extension == some "lean" then
    -- Top-level `.lean` file (e.g. `Main.lean`): instrument/arm directly below
    return false
  else
    let bytes ← IO.FS.readBinFile srcPath
    IO.FS.writeBinFile dstPath bytes
    return false

private def stageLakePackages (pkgAbs stageAbs : System.FilePath) : IO Unit := do
  let pkgDepsDir := pkgAbs / ".lake" / "packages"
  unless ← pkgDepsDir.isDir do return
  let stageDepsDir := stageAbs / ".lake" / "packages"
  IO.FS.createDirAll stageDepsDir
  for entry in (← pkgDepsDir.readDir) do
    forceSymlink entry.path (stageDepsDir / entry.fileName)

private structure StageAcc where
  nextId : Nat := 0
  sites : Array Site := #[]
  funcs : Array FuncInfo := #[]
  skipped : Array (String × String) := #[]
  armedAny : Bool := false

private def loadStageAcc (sitesOut : System.FilePath) (appendSites armedAny : Bool) : IO StageAcc := do
  if appendSites && (← sitesOut.pathExists) then
    let prev ← readManifest sitesOut
    return {
      nextId := prev.sites.size
      sites := prev.sites
      funcs := prev.functions
      skipped := prev.skippedFiles
      armedAny := armedAny || prev.armOnMain
    }
  return { armedAny }

private unsafe def stageInstrumentDirs (pkgAbs stageAbs : System.FilePath) (toInstrument : Array String)
    (pathPrefix : String) (cfg : InstrumentConfig) (acc : StageAcc) : IO StageAcc := do
  let mut st := acc
  for dirName in toInstrument do
    let dispPfx := if pathPrefix.isEmpty then dirName else s!"{pathPrefix}/{dirName}"
    let m ← instrumentTree (pkgAbs / dirName) (stageAbs / dirName) cfg st.nextId dispPfx (armMains := true)
    st := {
      nextId := st.nextId + m.sites.size
      sites := st.sites ++ m.sites
      funcs := st.funcs ++ m.functions
      skipped := st.skipped ++ m.skippedFiles
      armedAny := st.armedAny || m.armOnMain
    }
  return st

private def stageTopLevelLeanFile (env : Environment) (stageAbs : System.FilePath)
    (pathPrefix : String) (cfg : InstrumentConfig) (entry : IO.FS.DirEntry) (acc : StageAcc) :
    IO StageAcc := do
  let name := entry.fileName
  if name == "lakefile.lean" then return acc
  let p := entry.path
  if (← p.isDir) || p.extension != some "lean" then return acc
  let src ← IO.FS.readFile p
  let dispName := if pathPrefix.isEmpty then name else s!"{pathPrefix}/{name}"
  let excl := cfg.exclude.any fun pat => !pat.isEmpty && ((name.splitOn pat).length > 1 || (dispName.splitOn pat).length > 1)
  if excl then
    let (outSrc, armed) ← armMainInSource env dispName src
    IO.FS.writeFile (stageAbs / name) outSrc
    return { acc with armedAny := acc.armedAny || armed }
  let res ← instrumentSource env dispName src acc.nextId { cfg with armMains := true }
  let skipped := match res.skippedReason with
    | some why => acc.skipped.push (dispName, why)
    | none => acc.skipped
  IO.FS.writeFile (stageAbs / name) res.instrumented
  return {
    nextId := res.nextSiteId
    sites := acc.sites ++ res.sites
    funcs := acc.funcs ++ res.functions
    skipped := skipped
    armedAny := acc.armedAny || res.armedMain
  }

private def readTrimmedIfExists (p : System.FilePath) : IO (Option String) := do
  if !(← p.pathExists) then return none
  let txt ← IO.FS.readFile p
  let t := txt.trimAscii.copy
  return if t.isEmpty then none else some t

private def runtimeOnlyLakefile : String :=
"import Lake
open Lake DSL

package «leancov» where
  version := v!\"0.4.0\"

target leancov_rt.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / \"c\" / \"leancov_rt.o\"
  let srcJob ← inputTextFile <| pkg.dir / \"c\" / \"leancov_rt.c\"
  let weakArgs := #[\"-I\", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #[\"-fPIC\", \"-O2\", \"-std=c11\", \"-Wall\", \"-Wextra\"] \"cc\" getLeanTrace

extern_lib libleancov_rt pkg := do
  let name := nameToStaticLib \"leancov_rt\"
  let rtO ← leancov_rt.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[rtO]

lean_lib «LeanCov» where
  roots := #[`LeanCov.Runtime, `LeanCov.DoSyntax, `LeanCov.Check, `LeanCov.Fuzz]
  precompileModules := true
"

/-- When staging a package whose `lean-toolchain` differs from `leancov`'s own toolchain,
materialize a private runtime-only `.leancov-pkg` inside `stageAbs` so `lake build` never
clobbers `<leancovAbs>/.lake/build`. -/
private def prepareStageLeancovDep (pkgAbs stageAbs leancovAbs : System.FilePath) (isSelf : Bool) :
    IO System.FilePath := do
  if isSelf then return leancovAbs
  let some pkgTc ← readTrimmedIfExists (pkgAbs / "lean-toolchain") | return leancovAbs
  let some lcTc ← readTrimmedIfExists (leancovAbs / "lean-toolchain") | return leancovAbs
  if pkgTc == lcTc then return leancovAbs
  let localLc := stageAbs / ".leancov-pkg"
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", localLc.toString] }
  IO.FS.createDirAll (localLc / "c")
  IO.FS.createDirAll (localLc / "LeanCov")
  IO.FS.writeFile (localLc / "lean-toolchain") (pkgTc ++ "\n")
  IO.FS.writeFile (localLc / "lakefile.lean") runtimeOnlyLakefile
  IO.FS.writeFile (localLc / "c" / "leancov_rt.c") (← IO.FS.readFile (leancovAbs / "c" / "leancov_rt.c"))
  for f in #["Runtime.lean", "DoSyntax.lean", "Check.lean", "Fuzz.lean"] do
    let sp := leancovAbs / "LeanCov" / f
    if ← sp.pathExists then
      IO.FS.writeFile (localLc / "LeanCov" / f) (← IO.FS.readFile sp)
  return localLc

/-- Run `leancov stage`: create a clean out-of-tree instrumented copy of any Lake package. -/
private unsafe def cmdStage (args : List String) : IO UInt32 := do
  let opts ← match parseStageArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let some outDir := opts.stageDir | do
    IO.eprintln "stage: --out <stageDir> is required"
    return 2
  let pkgAbs ← canonicalOrAbs opts.pkgDir
  let (rawLeancovAbs, isSelf) ← match ← resolveLeancovDir pkgAbs opts with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  IO.FS.createDirAll outDir
  let stageAbs ← canonicalOrAbs outDir
  let leancovAbs ← prepareStageLeancovDep pkgAbs stageAbs rawLeancovAbs isSelf
  let depOverrides ← opts.depOverrides.mapM fun (k, p) => return (k, (← canonicalOrAbs ⟨p⟩).toString)
  let sitesOut := opts.sitesPath.getD (stageAbs / "sites.json")
  let cfg : InstrumentConfig := {
    exclude := opts.excludes
    extraImports := opts.extraImports
    instrumentBoolOps := opts.boolOps
    includeCafs := opts.includeCafs
  }

  let toInstrument ← discoverStageSrcDirs pkgAbs stageAbs opts.srcDirs
  let env ← loadParserEnv cfg.extraImports
  let mut armedAny := false
  for entry in (← pkgAbs.readDir) do
    if ← stageTopLevelEntry env pkgAbs stageAbs leancovAbs isSelf depOverrides toInstrument entry then
      armedAny := true

  -- Symlink existing `.lake/packages/*` individually so offline builds reuse them without modifying pkgAbs
  stageLakePackages pkgAbs stageAbs

  -- Instrument source directories and top-level `.lean` files
  let mut acc ← loadStageAcc sitesOut opts.appendSites armedAny
  acc ← stageInstrumentDirs pkgAbs stageAbs toInstrument opts.pathPrefix cfg acc
  for entry in (← pkgAbs.readDir) do
    acc ← stageTopLevelLeanFile env stageAbs opts.pathPrefix cfg entry acc

  let manifest : Manifest := {
    version := 1, armOnMain := acc.armedAny, sites := acc.sites, functions := acc.funcs, skippedFiles := acc.skipped
  }
  writeManifest sitesOut manifest
  IO.println s!"Staged {pkgAbs} -> {stageAbs}"
  IO.println s!"  Instrumented dirs: {", ".intercalate toInstrument.toList}"
  IO.println s!"  Declarations: {acc.funcs.size} | Probe sites: {acc.sites.size} | Manifest: {sitesOut}"
  if !acc.skipped.isEmpty then
    IO.eprintln s!"  Warning: {acc.skipped.size} file(s) skipped:"
    for (f, why) in acc.skipped do
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
  repeat
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
  LeanCov.raiseStack ()
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

private def collectGitChangedLines (repoDir : System.FilePath) (baseRef : String) :
    IO (Except String (Std.HashMap String (Array Nat))) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["-C", repoDir.toString, "diff", "-U0", baseRef, "--", "*.lean"]
  }
  if out.exitCode != 0 then
    return .error s!"git diff vs '{baseRef}' failed (exit {out.exitCode}): {out.stderr.trimAscii.copy}"
  return .ok (parseGitUnifiedDiff out.stdout)

/-- Run `leancov merge`: sum multiple `.cov` profiles into a single merged `.cov` file. -/
private def cmdMerge (args : List String) : IO UInt32 := do
  let mut outPath : Option System.FilePath := none
  let mut profiles : Array System.FilePath := #[]
  let mut rest := args
  repeat
    match rest with
    | "--out" :: v :: tl => outPath := some ⟨v⟩; rest := tl
    | "--profile" :: v :: tl => profiles := profiles.push ⟨v⟩; rest := tl
    | "--profile-dir" :: v :: tl =>
      profiles := profiles ++ (← collectCovFiles ⟨v⟩); rest := tl
    | flag :: _ =>
      IO.eprintln s!"unknown option for merge: {flag}"
      return 2
    | [] => break
  let some outP := outPath | do IO.eprintln "merge: --out <merged.cov> is required"; return 2
  if profiles.isEmpty then
    IO.eprintln "merge: at least one --profile <file.cov> or --profile-dir <dir> is required"
    return 2
  let mut maxSites := 0
  for p in profiles do
    let hits ← readProfile p
    if hits.size > maxSites then maxSites := hits.size
  let merged ← mergeProfiles profiles maxSites
  writeProfile outP merged
  IO.println s!"Merged {profiles.size} profile(s) ({maxSites} sites) -> {outP}"
  return 0

/-- Run `leancov report`. -/
private def cmdReport (args : List String) : IO UInt32 := do
  let mut sitesPath : Option System.FilePath := none
  let mut profiles : Array System.FilePath := #[]
  let mut jsonOut : Option System.FilePath := none
  let mut lcovOut : Option System.FilePath := none
  let mut mdOut : Option System.FilePath := none
  let mut htmlOut : Option System.FilePath := none
  let mut fileFilters : Array String := #[]
  let mut declFilters : Array String := #[]
  let mut excludeKinds : Array BranchKind := #[]
  let mut excludeInstances : Bool := false
  let mut topN : Nat := 25
  let mut sortBy : SortKey := .crap
  let mut showFiles : Bool := false
  let mut showKinds : Bool := false
  let mut showMissed : Bool := false
  let mut showMissedDetail : Bool := false
  let mut showHot : Bool := false
  let mut srcRoot : System.FilePath := "."
  let mut gitDiffRef : Option String := none
  let mut repoDir : System.FilePath := "."
  let mut minPatchCov : Option Float := none
  let mut minCov : Option Float := none
  let mut maxCrap : Option Float := none
  let mut maxCogCrap : Option Float := none
  let mut rest := args
  repeat
    match rest with
    | "--sites" :: v :: tl => sitesPath := some ⟨v⟩; rest := tl
    | "--profile" :: v :: tl => profiles := profiles.push ⟨v⟩; rest := tl
    | "--profile-dir" :: v :: tl =>
      profiles := profiles ++ (← collectCovFiles ⟨v⟩); rest := tl
    | "--json" :: v :: tl => jsonOut := some ⟨v⟩; rest := tl
    | "--lcov" :: v :: tl => lcovOut := some ⟨v⟩; rest := tl
    | "--markdown" :: v :: tl => mdOut := some ⟨v⟩; rest := tl
    | "--html" :: v :: tl => htmlOut := some ⟨v⟩; rest := tl
    | "--file" :: v :: tl => fileFilters := fileFilters ++ splitCommaNonEmpty v; rest := tl
    | "--decl" :: v :: tl => declFilters := declFilters ++ splitCommaNonEmpty v; rest := tl
    | "--exclude-kind" :: v :: tl =>
      for kTok in splitCommaNonEmpty v do
        match BranchKind.ofString? kTok with
        | some k => excludeKinds := excludeKinds.push k
        | none => IO.eprintln s!"invalid --exclude-kind value: {kTok}"; return 2
      rest := tl
    | "--exclude-instances" :: tl => excludeInstances := true; rest := tl
    | "--top" :: v :: tl =>
      match v.toNat? with
      | some n => topN := n; rest := tl
      | none => IO.eprintln s!"invalid --top value: {v}"; return 2
    | "--sort" :: v :: tl =>
      match SortKey.ofString? v with
      | some k => sortBy := k; rest := tl
      | none => IO.eprintln s!"invalid --sort value: {v} (use crap|cog|cc|uncov|cov)"; return 2
    | "--files" :: tl => showFiles := true; rest := tl
    | "--kinds" :: tl => showKinds := true; rest := tl
    | "--missed" :: tl => showMissed := true; rest := tl
    | "--missed-detail" :: tl => showMissedDetail := true; rest := tl
    | "--src-root" :: v :: tl => srcRoot := ⟨v⟩; rest := tl
    | "--hot" :: tl => showHot := true; rest := tl
    | "--git-diff" :: v :: tl => gitDiffRef := some v; rest := tl
    | "--repo" :: v :: tl => repoDir := ⟨v⟩; rest := tl
    | "--min-patch-cov" :: v :: tl =>
      match parseFloat? v with
      | some f => minPatchCov := some f; rest := tl
      | none => IO.eprintln s!"invalid --min-patch-cov value: {v}"; return 2
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
  let flt : ReportFilter := {
    files := fileFilters
    decls := declFilters
    excludeKinds := excludeKinds
    excludeInstances := excludeInstances
  }
  let mEff := filterManifest m flt
  let rep := buildReport mEff hits
  IO.println (formatReport rep topN sortBy showFiles showMissed showKinds)
  if showMissedDetail then
    let topFuncs := (sortFuncReports rep.functions sortBy).take (if topN == 0 then rep.functions.size else topN)
    let det ← formatMissedDetail mEff hits topFuncs srcRoot
    if !det.isEmpty then
      IO.println ("\n" ++ det)
  if showHot then
    IO.println ("\n" ++ formatHotSites mEff hits (if topN == 0 then 20 else topN))

  let patchOpt? : Option PatchReport ← match gitDiffRef with
    | none => pure none
    | some ref =>
      match ← collectGitChangedLines repoDir ref with
      | .error e => IO.eprintln s!"report: {e}"; return 2
      | .ok changed =>
        let pr := buildPatchReport mEff hits ref changed
        IO.println ("\n" ++ formatPatchReport pr)
        pure (some pr)

  if let some jp := jsonOut then
    if let some p := jp.parent then IO.FS.createDirAll p
    IO.FS.writeFile jp (toJson rep).pretty
  if let some lp := lcovOut then
    if let some p := lp.parent then IO.FS.createDirAll p
    IO.FS.writeFile lp (toLcov mEff hits)
  if let some mp := mdOut then
    if let some p := mp.parent then IO.FS.createDirAll p
    IO.FS.writeFile mp (formatReportMarkdown rep topN sortBy patchOpt?)
  if let some hd := htmlOut then
    writeHtmlReport hd srcRoot mEff hits rep

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
  if let (some mpc, some pr) := (minPatchCov, patchOpt?) then
    if pr.sitesTotal > 0 && pr.branchCov * 100.0 < mpc then
      IO.eprintln s!"FAIL: patch branch coverage {pr.branchCov * 100.0}% < --min-patch-cov {mpc}%"
      failed := true
  return if failed then 1 else 0

private def readSummaryJson (path : System.FilePath) : IO SummaryReport := do
  let raw ← IO.FS.readFile path
  match Json.parse raw >>= fromJson? with
  | .ok r => return r
  | .error e => throw (IO.userError s!"{path}: invalid report JSON: {e}")

/-- Run `leancov diff`: compare two coverage JSON reports and gate regressions. -/
private def cmdDiff (args : List String) : IO UInt32 := do
  let mut basePath : Option System.FilePath := none
  let mut headPath : Option System.FilePath := none
  let mut jsonOut : Option System.FilePath := none
  let mut mdOut : Option System.FilePath := none
  let mut topN : Nat := 15
  let mut maxCovDrop : Option Float := none
  let mut maxCrapDelta : Option Float := none
  let mut rest := args
  repeat
    match rest with
    | "--base" :: v :: tl => basePath := some ⟨v⟩; rest := tl
    | "--head" :: v :: tl => headPath := some ⟨v⟩; rest := tl
    | "--json" :: v :: tl => jsonOut := some ⟨v⟩; rest := tl
    | "--markdown" :: v :: tl => mdOut := some ⟨v⟩; rest := tl
    | "--top" :: v :: tl =>
      match v.toNat? with
      | some n => topN := n; rest := tl
      | none => IO.eprintln s!"invalid --top value: {v}"; return 2
    | "--max-cov-drop" :: v :: tl =>
      match parseFloat? v with
      | some f => maxCovDrop := some f; rest := tl
      | none => IO.eprintln s!"invalid --max-cov-drop value: {v}"; return 2
    | "--max-crap-delta" :: v :: tl =>
      match parseFloat? v with
      | some f => maxCrapDelta := some f; rest := tl
      | none => IO.eprintln s!"invalid --max-crap-delta value: {v}"; return 2
    | flag :: _ =>
      IO.eprintln s!"unknown option for diff: {flag}"
      return 2
    | [] => break
  let some bp := basePath | do IO.eprintln "diff: --base <old.json> is required"; return 2
  let some hp := headPath | do IO.eprintln "diff: --head <new.json> is required"; return 2
  let baseRep ← readSummaryJson bp
  let headRep ← readSummaryJson hp
  let d := computeDiffReport baseRep headRep
  IO.println (formatDiffReport d topN)
  if let some jp := jsonOut then
    if let some p := jp.parent then IO.FS.createDirAll p
    IO.FS.writeFile jp (toJson d).pretty
  if let some mp := mdOut then
    if let some p := mp.parent then IO.FS.createDirAll p
    IO.FS.writeFile mp (formatDiffMarkdown d topN)
  let mut failed := false
  if let some mcd := maxCovDrop then
    let dropPct := -d.branchCovDelta * 100.0
    if dropPct > mcd then
      IO.eprintln s!"FAIL: branch coverage dropped by {dropPct}% > --max-cov-drop {mcd}%"
      failed := true
  if let some mxd := maxCrapDelta then
    if d.maxCogCrapDelta > mxd || d.maxCrapDelta > mxd then
      IO.eprintln s!"FAIL: max CRAP delta (cog={d.maxCogCrapDelta}, mccabe={d.maxCrapDelta}) > --max-crap-delta {mxd}"
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
  repeat
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

private structure MutateOpts where
  pkgDir : System.FilePath := "."
  workDir : Option System.FilePath := none
  files : Array String := #[]
  srcDirs : Array String := #[]
  filters : Array String := #[]
  kinds : Array MutantKind := #[]
  jobs : Nat := 1
  maxMutants : Option Nat := none
  seed : Option UInt64 := none
  timeoutMs : Nat := 30000
  buildTargets : Array String := #[]
  proofTargets : Array String := #[]
  noBuild : Bool := false
  includeArith : Bool := true
  includeInterp : Bool := false
  sitesPath : Option System.FilePath := none
  profiles : Array System.FilePath := #[]
  gitDiffRef : Option String := none
  extraImports : Array Name := #[]
  jsonOut : Option System.FilePath := none
  mdOut : Option System.FilePath := none
  minScore : Option Float := none
  keepWork : Bool := false
  cmdArgs : List String := []
  deriving Inhabited

private def parseSeedUInt64? (s : String) : Option UInt64 :=
  if s.startsWith "0x" then
    let hexDigits := (s.drop 2).toString
    if hexDigits.isEmpty then none
    else
      let val? := hexDigits.foldl (fun acc c => do
        let d ←
          if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
          else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
          else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
          else none
        some ((← acc) * 16 + d)) (some 0)
      val?.map Nat.toUInt64
  else s.toNat?.map Nat.toUInt64

private def parseMutateArgs : List String → MutateOpts → IO (Except String MutateOpts)
  | [], o => pure (.ok o)
  | "--pkg" :: v :: tl, o => parseMutateArgs tl { o with pkgDir := ⟨v⟩ }
  | "--out" :: v :: tl, o => parseMutateArgs tl { o with workDir := some ⟨v⟩ }
  | "--file" :: v :: tl, o => parseMutateArgs tl { o with files := o.files.push v }
  | "--src-dir" :: v :: tl, o => parseMutateArgs tl { o with srcDirs := o.srcDirs.push v }
  | "--filter" :: v :: tl, o => parseMutateArgs tl { o with filters := o.filters ++ splitCommaNonEmpty v }
  | "--kinds" :: v :: tl, o => do
    let mut ks := o.kinds
    for tok in splitCommaNonEmpty v do
      match MutantKind.ofAlias? tok with
      | some k => ks := ks.push k
      | none => return .error s!"invalid --kinds value: {tok} (use cmp|arith|bool|lit|neg|cond)"
    parseMutateArgs tl { o with kinds := ks }
  | "--jobs" :: v :: tl, o =>
    match v.toNat? with
    | some n =>
      if n ≥ 1 then parseMutateArgs tl { o with jobs := n }
      else pure (.error s!"--jobs must be >= 1: {v}")
    | none => pure (.error s!"invalid --jobs value: {v}")
  | "--max-mutants" :: v :: tl, o =>
    match v.toNat? with
    | some n => parseMutateArgs tl { o with maxMutants := some n }
    | none => pure (.error s!"invalid --max-mutants value: {v}")
  | "--seed" :: v :: tl, o =>
    match parseSeedUInt64? v with
    | some s => parseMutateArgs tl { o with seed := some s }
    | none => pure (.error s!"invalid --seed value: {v}")
  | "--timeout" :: v :: tl, o =>
    match parseFloat? v with
    | some f =>
      if f > 0.0 then parseMutateArgs tl { o with timeoutMs := max 1 (f * 1000.0).toUInt64.toNat }
      else pure (.error s!"--timeout must be > 0: {v}")
    | none => pure (.error s!"invalid --timeout value: {v}")
  | "--build-target" :: v :: tl, o => parseMutateArgs tl { o with buildTargets := o.buildTargets.push v }
  | "--proof-target" :: v :: tl, o => parseMutateArgs tl { o with proofTargets := o.proofTargets.push v }
  | "--no-build" :: tl, o => parseMutateArgs tl { o with noBuild := true }
  | "--no-arith" :: tl, o => parseMutateArgs tl { o with includeArith := false }
  | "--include-interp" :: tl, o => parseMutateArgs tl { o with includeInterp := true }
  | "--sites" :: v :: tl, o => parseMutateArgs tl { o with sitesPath := some ⟨v⟩ }
  | "--profile" :: v :: tl, o => parseMutateArgs tl { o with profiles := o.profiles.push ⟨v⟩ }
  | "--profile-dir" :: v :: tl, o => do
    let covs ← collectCovFiles ⟨v⟩
    parseMutateArgs tl { o with profiles := o.profiles ++ covs }
  | "--git-diff" :: v :: tl, o => parseMutateArgs tl { o with gitDiffRef := some v }
  | "--imports" :: v :: tl, o => parseMutateArgs tl { o with extraImports := o.extraImports ++ splitImports v }
  | "--json" :: v :: tl, o => parseMutateArgs tl { o with jsonOut := some ⟨v⟩ }
  | "--markdown" :: v :: tl, o => parseMutateArgs tl { o with mdOut := some ⟨v⟩ }
  | "--min-score" :: v :: tl, o =>
    match parseFloat? v with
    | some f => parseMutateArgs tl { o with minScore := some f }
    | none => pure (.error s!"invalid --min-score value: {v}")
  | "--keep-work" :: tl, o => parseMutateArgs tl { o with keepWork := true }
  | "--" :: tl, o => pure (.ok { o with cmdArgs := tl })
  | tok :: tl, o =>
    if tok.startsWith "-" then pure (.error s!"unknown option for mutate: {tok}")
    else pure (.ok { o with cmdArgs := tok :: tl })

private def resolveInsidePkg (callerCwd pkgAbs : System.FilePath) (raw : String) :
    IO (Option System.FilePath) := do
  let p1 := pkgAbs / raw
  if ← p1.pathExists then return some (← canonicalOrAbs p1)
  let p2 := if (⟨raw⟩ : System.FilePath).isAbsolute then (⟨raw⟩ : System.FilePath) else callerCwd / raw
  if ← p2.pathExists then
    let abs ← canonicalOrAbs p2
    if isPrefixPath pkgAbs abs then return some abs
  return none

private def collectMutateRelFiles (callerCwd pkgAbs : System.FilePath) (opts : MutateOpts) :
    IO (Except String (Array String)) := do
  if opts.files.isEmpty && opts.srcDirs.isEmpty then
    return .error "mutate: at least one --file <relFile> or --src-dir <relDir> is required"
  let mut rels : Array String := #[]
  for f in opts.files do
    let some abs ← resolveInsidePkg callerCwd pkgAbs f
      | return .error s!"mutate: file not found inside package: {f}"
    let r := relativeTo pkgAbs abs
    if !rels.contains r then rels := rels.push r
  for d in opts.srcDirs do
    let some absDir ← resolveInsidePkg callerCwd pkgAbs d
      | return .error s!"mutate: directory not found inside package: {d}"
    for lf in (← collectLeanFiles absDir) do
      let r := relativeTo pkgAbs lf
      if !rels.contains r then rels := rels.push r
  if rels.isEmpty then
    return .error "mutate: no .lean files matched --file / --src-dir"
  return .ok rels

private partial def hasNestedIgnoredDir (dir : System.FilePath) : IO Bool := do
  for name in #[".git", ".lake", "build"] do
    if ← (dir / name).pathExists then return true
  for entry in (← dir.readDir) do
    let sp := entry.path
    if ← sp.isDir then
      if ← hasNestedIgnoredDir sp then return true
  return false

private partial def copyCleanDir (srcDir dstDir skipAbs : System.FilePath) : IO Unit := do
  if !isPrefixPath srcDir skipAbs && !isPrefixPath skipAbs srcDir && !(← hasNestedIgnoredDir srcDir) then
    if let some p := dstDir.parent then IO.FS.createDirAll p
    let _ ← IO.Process.output { cmd := "cp", args := #["-Rp", srcDir.toString, dstDir.toString] }
    return
  IO.FS.createDirAll dstDir
  for entry in (← srcDir.readDir) do
    let name := entry.fileName
    if isIgnoredDirName name then continue
    let sp := entry.path
    if isPrefixPath sp skipAbs || isPrefixPath skipAbs sp then continue
    let dp := dstDir / name
    if ← sp.isDir then
      copyCleanDir sp dp skipAbs
    else
      let _ ← IO.Process.output { cmd := "cp", args := #["-p", sp.toString, dp.toString] }

private def warmLakeBuildCache (pkgAbs workAbs : System.FilePath) : IO Unit := do
  for rel in #["ir", "lib/lean", "c"] do
    let srcSub := pkgAbs / ".lake" / "build" / rel
    if ← srcSub.isDir then
      let dstSub := workAbs / ".lake" / "build" / rel
      if let some p := dstSub.parent then IO.FS.createDirAll p
      let _ ← IO.Process.output { cmd := "cp", args := #["-R", srcSub.toString, dstSub.toString] }

private def stageMutateWorkspace (pkgAbs workAbs : System.FilePath) : IO Unit := do
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", workAbs.toString] }
  IO.FS.createDirAll workAbs
  for entry in (← pkgAbs.readDir) do
    let name := entry.fileName
    if isIgnoredDirName name then continue
    let sp := entry.path
    if isPrefixPath sp workAbs || isPrefixPath workAbs sp then continue
    let dp := workAbs / name
    if name == "lakefile.lean" then
      let txt ← IO.FS.readFile sp
      IO.FS.writeFile dp (rewriteLakefileLean txt pkgAbs pkgAbs (isSelf := true))
    else if name == "lakefile.toml" then
      let txt ← IO.FS.readFile sp
      IO.FS.writeFile dp (rewriteLakefileToml txt pkgAbs pkgAbs (isSelf := true))
    else if name == "lake-manifest.json" then
      stageLakeManifest pkgAbs workAbs pkgAbs (isSelf := true)
    else if ← sp.isDir then
      copyCleanDir sp dp workAbs
    else
      let _ ← IO.Process.output { cmd := "cp", args := #["-p", sp.toString, dp.toString] }
  stageLakePackages pkgAbs workAbs
  warmLakeBuildCache pkgAbs workAbs

private def resolveMutateTestCmd (callerCwd pkgAbs workAbs : System.FilePath) (rawCmd : String) :
    IO (Except String String) := do
  let checkNotUnmutated (abs : System.FilePath) : Except String String :=
    if !isPrefixPath workAbs abs && isPrefixPath (pkgAbs / ".lake") abs then
      .error s!"mutate: test command '{rawCmd}' points inside unmutated --pkg/.lake; use '.lake/build/bin/<exe>' so it runs from the staged workspace"
    else .ok abs.toString
  let fp : System.FilePath := ⟨rawCmd⟩
  if fp.isAbsolute then
    return checkNotUnmutated (← canonicalOrAbs fp)
  if (rawCmd.splitOn "/").length > 1 then
    if ← (workAbs / rawCmd).pathExists then
      return .ok (← canonicalOrAbs (workAbs / rawCmd)).toString
    if ← (callerCwd / rawCmd).pathExists then
      return checkNotUnmutated (← canonicalOrAbs (callerCwd / rawCmd))
  return .ok rawCmd

private def removeWorkDirUnlessKept (workAbs : System.FilePath) (keep : Bool) : IO Unit := do
  unless keep do
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", workAbs.toString] }

/-- Run `leancov mutate`: AST-guided mutation testing in an isolated staged Lake workspace. -/
private unsafe def cmdMutate (args : List String) : IO UInt32 := do
  let opts ← match ← parseMutateArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let rawCmd :: cmdRest := opts.cmdArgs | do
    IO.eprintln "mutate: -- <testCmd> [args...] is required"
    return 2
  if opts.sitesPath.isSome && opts.profiles.isEmpty then
    IO.eprintln "mutate: --sites requires at least one --profile or --profile-dir"
    return 2
  if opts.sitesPath.isNone && !opts.profiles.isEmpty then
    IO.eprintln "mutate: --profile / --profile-dir requires --sites <sites.json>"
    return 2
  let callerCwd ← IO.currentDir
  let pkgAbs ← canonicalOrAbs opts.pkgDir
  let relFiles ← match ← collectMutateRelFiles callerCwd pkgAbs opts with
    | .ok fs => pure fs
    | .error e => IO.eprintln e; return 2
  let env ← loadParserEnv opts.extraImports
  let mut origByFile : Std.HashMap String String := {}
  let mut allMutants : Array Mutant := #[]
  for rel in relFiles do
    let src ← IO.FS.readFile (pkgAbs / rel)
    origByFile := origByFile.insert rel src
    let ms ← discoverMutantsInSource env rel src allMutants.size opts.filters opts.includeArith opts.includeInterp
    allMutants := allMutants ++ ms
  allMutants := filterMutantsByKinds allMutants opts.kinds
  if let some ref := opts.gitDiffRef then
    match ← collectGitChangedLines pkgAbs ref with
    | .error e => IO.eprintln s!"mutate: {e}"; return 2
    | .ok changed => allMutants := filterMutantsByGitDiff allMutants changed
  let discovered := allMutants.size
  let sampled := match opts.maxMutants with
    | some n => sampleMutants allMutants n opts.seed
    | none => sampleMutants allMutants allMutants.size opts.seed
  let (selected, preUncovered) ← match opts.sitesPath with
    | none => pure (sampled, (#[] : Array MutantResult))
    | some sp =>
      let m ← readManifest sp
      let hits ← mergeProfiles opts.profiles m.sites.size
      pure (pruneUncoveredMutants sampled m hits)
  let defaultWork := pkgAbs / ".lake" / "build" / "leancov-mutate"
  let rawWork := opts.workDir.getD defaultWork
  IO.FS.createDirAll rawWork
  let workAbs ← canonicalOrAbs rawWork
  IO.println s!"Staging clean mutation workspace: {pkgAbs} -> {workAbs}"
  let uncovMsg := if preUncovered.isEmpty then "" else s!" | Pruned uncovered: {preUncovered.size}"
  IO.println s!"  Target files: {relFiles.size} | Mutants discovered: {discovered} | Running: {selected.size}{uncovMsg}"
  stageMutateWorkspace pkgAbs workAbs
  let cfg : MutateRunConfig := {
    workDir := workAbs
    buildTargets := opts.buildTargets
    proofTargets := opts.proofTargets
    noBuild := opts.noBuild
    testCmd := rawCmd
    testArgs := cmdRest.toArray
    timeoutMs := opts.timeoutMs
    jobs := opts.jobs
  }
  let res ← try
    executeMutants cfg origByFile discovered selected (resolveMutateTestCmd callerCwd pkgAbs workAbs rawCmd) preUncovered
  catch e =>
    removeWorkDirUnlessKept workAbs opts.keepWork
    throw e
  removeWorkDirUnlessKept workAbs opts.keepWork
  let rep ← match res with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  IO.println (formatMutateReport rep)
  if let some jp := opts.jsonOut then
    if let some p := jp.parent then IO.FS.createDirAll p
    IO.FS.writeFile jp (toJson rep).pretty
  if let some mp := opts.mdOut then
    if let some p := mp.parent then IO.FS.createDirAll p
    IO.FS.writeFile mp (formatMutateMarkdown rep)
  if let some ms := opts.minScore then
    if rep.score < ms then
      IO.eprintln s!"FAIL: mutation score {rep.score}% < --min-score {ms}%"
      return 1
  return 0

private structure TestOpts where
  configPath : System.FilePath := "leancov.toml"
  leancovDir : Option System.FilePath := none
  fastMode : Bool := false
  cleanMode : Bool := false
  noBuild : Bool := false
  reportOnly : Bool := false
  listOnly : Bool := false
  jobs? : Option Nat := none
  sort? : Option SortKey := none
  top? : Option Nat := none
  htmlDir? : Option System.FilePath := none
  mdFile? : Option System.FilePath := none
  excludeInstances : Bool := false
  minCov? : Option Float := none
  maxCrap? : Option Float := none
  maxCogCrap? : Option Float := none
  suites : Array String := #[]
  deriving Inhabited

private def parseTestArgs : List String → TestOpts → Except String TestOpts
  | [], o => pure o
  | "--config" :: v :: tl, o => parseTestArgs tl { o with configPath := ⟨v⟩ }
  | "--leancov" :: v :: tl, o => parseTestArgs tl { o with leancovDir := some ⟨v⟩ }
  | "--fast" :: tl, o => parseTestArgs tl { o with fastMode := true }
  | "--clean" :: tl, o => parseTestArgs tl { o with cleanMode := true }
  | "--no-build" :: tl, o => parseTestArgs tl { o with noBuild := true }
  | "--report" :: tl, o => parseTestArgs tl { o with reportOnly := true }
  | "--list" :: tl, o => parseTestArgs tl { o with listOnly := true }
  | "--jobs" :: v :: tl, o =>
    match v.toNat? with
    | some n => if n ≥ 1 then parseTestArgs tl { o with jobs? := some n } else throw s!"--jobs must be >= 1: {v}"
    | none => throw s!"invalid --jobs value: {v}"
  | "--sort" :: v :: tl, o =>
    match SortKey.ofString? v with
    | some k => parseTestArgs tl { o with sort? := some k }
    | none => throw s!"invalid --sort value: {v}"
  | "--top" :: v :: tl, o =>
    match v.toNat? with
    | some n => parseTestArgs tl { o with top? := some n }
    | none => throw s!"invalid --top value: {v}"
  | "--html" :: v :: tl, o => parseTestArgs tl { o with htmlDir? := some ⟨v⟩ }
  | "--markdown" :: v :: tl, o => parseTestArgs tl { o with mdFile? := some ⟨v⟩ }
  | "--exclude-instances" :: tl, o => parseTestArgs tl { o with excludeInstances := true }
  | "--min-cov" :: v :: tl, o =>
    match parseFloat? v with
    | some f => parseTestArgs tl { o with minCov? := some f }
    | none => throw s!"invalid --min-cov value: {v}"
  | "--max-crap" :: v :: tl, o =>
    match parseFloat? v with
    | some f => parseTestArgs tl { o with maxCrap? := some f }
    | none => throw s!"invalid --max-crap value: {v}"
  | "--max-cog-crap" :: v :: tl, o =>
    match parseFloat? v with
    | some f => parseTestArgs tl { o with maxCogCrap? := some f }
    | none => throw s!"invalid --max-cog-crap value: {v}"
  | tok :: tl, o =>
    if tok.startsWith "-" then throw s!"unknown option for test: {tok}"
    else parseTestArgs tl { o with suites := o.suites.push tok }

private def resolveFromRoot (root : System.FilePath) (raw : String) : System.FilePath :=
  let p : System.FilePath := ⟨raw⟩
  if p.isAbsolute then p else root / p

private def runSuiteWorker (outDir rootDir : System.FilePath) (cfg : ProjectConfig)
    (armOnMain : Bool) (siteCount : Nat)
    (queueRef : Std.Mutex (List SuiteConfig)) (printMutex : Std.Mutex Unit) :
    IO (Array (String × UInt32)) := do
  let profilesDir := outDir / "profiles"
  let logsDir := outDir / "logs"
  let mut out : Array (String × UInt32) := #[]
  repeat
    let next? ← queueRef.atomically do
      match ← get with
      | [] => return none
      | s :: rest => set rest; return some s
    let some s := next? | break
    let profPath := profilesDir / s!"{s.name}.cov"
    initProfile profPath siteCount
    let mut envVars : Array (String × Option String) := #[
      ("LEAN_COV_FILE", some profPath.toString),
      ("LEAN_COV_SITES", some (toString siteCount))
    ]
    if armOnMain then envVars := envVars.push ("LEAN_COV_DEFER_INIT", some "1")
    let pkgCwd := match s.cwd with
      | some c => resolveFromRoot rootDir c
      | none =>
        let pRel := (cfg.packages.find? (·.name == s.package)).map (·.pkg) |>.getD "."
        resolveFromRoot rootDir pRel
    let binPath := outDir / s.package / ".lake" / "build" / "bin" / s.target
    let proc ← IO.Process.output {
      cmd := binPath.toString
      args := s.args
      cwd := some pkgCwd
      env := envVars
    }
    IO.FS.writeFile (logsDir / s!"{s.name}.log") (proc.stdout ++ proc.stderr)
    printMutex.atomically do
      let mark := if proc.exitCode == 0 then "ok  " else "FAIL"
      IO.println s!"  {mark} {s.name} (exit {proc.exitCode})"
    out := out.push (s.name, proc.exitCode)
  return out

/-- Run `leancov test`: declarative multi-package staging, parallel execution, and reporting from `leancov.toml`. -/
private unsafe def cmdTest (args : List String) : IO UInt32 := do
  let opts ← match parseTestArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  unless ← opts.configPath.pathExists do
    IO.eprintln s!"test: config file not found: {opts.configPath}"
    return 2
  let cfg ← match parseProjectConfig (← IO.FS.readFile opts.configPath) with
    | .ok c => pure c
    | .error e => IO.eprintln s!"test: {opts.configPath}: {e}"; return 2
  if opts.listOnly then
    for s in cfg.suites do
      let tier := if s.fast then "fast" else "full"
      IO.println s!"  {s.name}  ({s.package}:{s.target}, {tier})"
    return 0
  let mut selected : Array SuiteConfig := #[]
  if !opts.suites.isEmpty then
    for nm in opts.suites do
      match cfg.suites.find? (·.name == nm) with
      | some s => selected := selected.push s
      | none => IO.eprintln s!"test: unknown suite '{nm}'"; return 2
  else
    selected := if opts.fastMode then cfg.suites.filter (·.fast) else cfg.suites
  if selected.isEmpty then
    IO.eprintln "test: no suites selected to run"
    return 2

  let cfgAbs ← canonicalOrAbs opts.configPath
  let rootDir := cfgAbs.parent.getD ⟨"."⟩
  let outDir := resolveFromRoot rootDir cfg.out
  let sitesPath := outDir / "sites.json"
  let profilesDir := outDir / "profiles"
  let logsDir := outDir / "logs"

  let mut failedSuites : Array String := #[]
  unless opts.reportOnly do
    if opts.cleanMode then
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", outDir.toString] }
    unless opts.noBuild do
      if ← sitesPath.pathExists then
        let _ ← IO.Process.output { cmd := "rm", args := #["-f", sitesPath.toString] }
      for idx in [:cfg.packages.size] do
        let p := cfg.packages[idx]!
        let mut stArgs : List String := [
          "--pkg", (resolveFromRoot rootDir p.pkg).toString,
          "--out", (outDir / p.name).toString,
          "--sites", sitesPath.toString
        ]
        if let some ld := opts.leancovDir then stArgs := stArgs ++ ["--leancov", ld.toString]
        if idx > 0 then stArgs := stArgs ++ ["--append-sites"]
        if !p.pathPrefix.isEmpty then stArgs := stArgs ++ ["--prefix", p.pathPrefix]
        for sd in p.srcDirs do stArgs := stArgs ++ ["--src-dir", sd]
        for ex in p.exclude do stArgs := stArgs ++ ["--exclude", ex]
        for imp in p.imports do stArgs := stArgs ++ ["--imports", imp]
        for d in p.deps do
          let depVal := match d.splitOn "=" with
            | [dn, dv] =>
              if cfg.packages.any (·.name == dv) then s!"{dn}={outDir / dv}"
              else s!"{dn}={resolveFromRoot rootDir dv}"
            | _ => d
          stArgs := stArgs ++ ["--dep", depVal]
        if !p.boolOps then stArgs := stArgs ++ ["--no-bool-ops"]
        if p.includeCafs then stArgs := stArgs ++ ["--include-cafs"]
        let stCode ← cmdStage stArgs
        if stCode != 0 then return stCode
      for p in cfg.packages do
        let mut targets : Array String := #[]
        for s in selected do
          if s.package == p.name && !targets.contains s.target then
            targets := targets.push s.target
        if !targets.isEmpty then
          IO.println s!"Building {p.name} target(s): {", ".intercalate targets.toList}"
          let bOut ← IO.Process.output {
            cmd := "lake"
            args := #["build"] ++ targets
            cwd := some (outDir / p.name)
          }
          if bOut.exitCode != 0 then
            IO.eprintln s!"test: lake build failed in {outDir / p.name}:\n{bOut.stdout}{bOut.stderr}"
            return 1
    unless ← sitesPath.pathExists do
      IO.eprintln s!"test: {sitesPath} not found; run without --no-build first"
      return 2
    let m ← readManifest sitesPath
    if opts.suites.isEmpty && !opts.fastMode then
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", profilesDir.toString, logsDir.toString] }
    IO.FS.createDirAll profilesDir
    IO.FS.createDirAll logsDir
    let jobs := max 1 (opts.jobs?.getD cfg.jobs)
    let nWorkers := min jobs selected.size
    IO.println s!"Running {selected.size} suite(s) with {nWorkers} worker(s)..."
    LeanCov.raiseStack ()
    let queueRef ← Std.Mutex.new selected.toList
    let printMutex ← Std.Mutex.new ()
    let mut tasks : Array (Task (Except IO.Error (Array (String × UInt32)))) := #[]
    for _ in [:nWorkers] do
      let t ← IO.asTask (prio := .dedicated) (runSuiteWorker outDir rootDir cfg m.armOnMain m.sites.size queueRef printMutex)
      tasks := tasks.push t
    for t in tasks do
      let res ← IO.ofExcept (← IO.wait t)
      for (sn, code) in res do
        if code != 0 then failedSuites := failedSuites.push sn

  unless ← sitesPath.pathExists do
    IO.eprintln s!"test: {sitesPath} not found; run suites first"
    return 2

  let subsetReport := opts.reportOnly && (!opts.suites.isEmpty || opts.fastMode)
  let mut repArgs : List String := ["--sites", sitesPath.toString]
  if subsetReport then
    for s in selected do
      repArgs := repArgs ++ ["--profile", (profilesDir / s!"{s.name}.cov").toString]
  else
    repArgs := repArgs ++ ["--profile-dir", profilesDir.toString]
  repArgs := repArgs ++ [
    "--json", (outDir / "coverage.json").toString,
    "--lcov", (outDir / "lcov.info").toString,
    "--sort", (opts.sort?.getD cfg.sort).toString,
    "--top", toString (opts.top?.getD cfg.top),
    "--src-root", rootDir.toString
  ]
  if cfg.files then repArgs := repArgs ++ ["--files"]
  if cfg.kinds then repArgs := repArgs ++ ["--kinds"]
  if opts.excludeInstances || cfg.excludeInstances then repArgs := repArgs ++ ["--exclude-instances"]
  for ek in cfg.excludeKinds do repArgs := repArgs ++ ["--exclude-kind", ek.toString]
  if let some hd := opts.htmlDir? then repArgs := repArgs ++ ["--html", hd.toString]
  else if cfg.html then repArgs := repArgs ++ ["--html", (outDir / "html").toString]
  if let some md := opts.mdFile? then repArgs := repArgs ++ ["--markdown", md.toString]
  else if cfg.markdown then repArgs := repArgs ++ ["--markdown", (outDir / "report.md").toString]
  if let some mc := opts.minCov?.orElse (fun _ => cfg.minCov) then repArgs := repArgs ++ ["--min-cov", toString mc]
  if let some xc := opts.maxCrap?.orElse (fun _ => cfg.maxCrap) then repArgs := repArgs ++ ["--max-crap", toString xc]
  if let some xg := opts.maxCogCrap?.orElse (fun _ => cfg.maxCogCrap) then repArgs := repArgs ++ ["--max-cog-crap", toString xg]
  let repCode ← cmdReport repArgs
  if !failedSuites.isEmpty then
    IO.eprintln s!"test: failed suite(s): {", ".intercalate failedSuites.toList} (logs in {logsDir})"
    return 1
  return repCode

unsafe def runCLI (args : List String) : IO UInt32 := do
  match args with
  | "instrument" :: rest => cmdInstrument rest
  | "stage" :: rest => cmdStage rest
  | "run" :: rest => cmdRun rest
  | "merge" :: rest => cmdMerge rest
  | "report" :: rest => cmdReport rest
  | "test" :: rest => cmdTest rest
  | "diff" :: rest => cmdDiff rest
  | "analyze" :: rest => cmdAnalyze rest
  | "mutate" :: rest => cmdMutate rest
  | "--version" :: _ | "-V" :: _ =>
    IO.println s!"leancov {version}"
    return 0
  | "--help" :: _ | "-h" :: _ | "help" :: _ | [] =>
    IO.println usage
    return 0
  | cmd :: _ =>
    IO.eprintln s!"unknown subcommand: {cmd}\n\n{usage}"
    return 2

end LeanCov.CLI
