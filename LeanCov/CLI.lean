import Lean.Data.Json
import LeanCov.Runtime
import LeanCov.Cov

/-! # `leancov` CLI

Subcommands:
- `leancov instrument` — rewrite Lean source trees with source-level coverage probes and write `sites.json`
- `leancov stage`      — stage an entire Lake package into an out-of-tree instrumented build directory
- `leancov run`        — execute a command with `LEAN_COV_FILE` / `LEAN_COV_SITES` initialized
- `leancov report`     — merge `.cov` profiles, print CRAP/Cognitive-CRAP summary, export JSON & LCOV
- `leancov analyze`    — static McCabe CC and Cognitive Complexity report without running tests
- `leancov mutate`     — AST-guided mutation testing in an isolated staged Lake workspace -/

namespace LeanCov.CLI
open Lean LeanCov.Cov

/-- Package version printed by `leancov --version` / `-V`. -/
def version : String := "0.1.0"

private def usage : String :=
"leancov — source-level Lean 4 coverage, McCabe CRAP, Cognitive Complexity, and AST Mutation Testing

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
  leancov mutate     --pkg <pkgDir> [--out <workDir>] (--file <relFile> | --src-dir <relDir>)...
                     [--filter <declSubstr>]... [--max-mutants <N>] [--timeout <sec>]
                     [--build-target <lakeTarget>]... [--no-build] [--imports <Mod1,Mod2>]...
                     [--json <out.json>] [--min-score <pct>] [--keep-work] -- <testCmd> [args...]
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
  version := v!\"0.1.0\"

target leancov_rt.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / \"c\" / \"leancov_rt.o\"
  let srcJob ← inputTextFile <| pkg.dir / \"c\" / \"leancov_rt.c\"
  let weakArgs := #[\"-I\", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #[\"-fPIC\", \"-O2\", \"-Wall\", \"-Wextra\"] \"cc\" getLeanTrace

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
  repeat
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
  maxMutants : Option Nat := none
  timeoutMs : Nat := 30000
  buildTargets : Array String := #[]
  noBuild : Bool := false
  extraImports : Array Name := #[]
  jsonOut : Option System.FilePath := none
  minScore : Option Float := none
  keepWork : Bool := false
  cmdArgs : List String := []
  deriving Inhabited

private def splitCommaNonEmpty (s : String) : Array String :=
  (s.splitOn ",").toArray.filterMap fun p =>
    let t := p.trimAscii.copy
    if t.isEmpty then none else some t

private def parseMutateArgs : List String → MutateOpts → Except String MutateOpts
  | [], o => pure o
  | "--pkg" :: v :: tl, o => parseMutateArgs tl { o with pkgDir := ⟨v⟩ }
  | "--out" :: v :: tl, o => parseMutateArgs tl { o with workDir := some ⟨v⟩ }
  | "--file" :: v :: tl, o => parseMutateArgs tl { o with files := o.files.push v }
  | "--src-dir" :: v :: tl, o => parseMutateArgs tl { o with srcDirs := o.srcDirs.push v }
  | "--filter" :: v :: tl, o => parseMutateArgs tl { o with filters := o.filters ++ splitCommaNonEmpty v }
  | "--max-mutants" :: v :: tl, o =>
    match v.toNat? with
    | some n => parseMutateArgs tl { o with maxMutants := some n }
    | none => throw s!"invalid --max-mutants value: {v}"
  | "--timeout" :: v :: tl, o =>
    match parseFloat? v with
    | some f =>
      if f > 0.0 then parseMutateArgs tl { o with timeoutMs := max 1 (f * 1000.0).toUInt64.toNat }
      else throw s!"--timeout must be > 0: {v}"
    | none => throw s!"invalid --timeout value: {v}"
  | "--build-target" :: v :: tl, o => parseMutateArgs tl { o with buildTargets := o.buildTargets.push v }
  | "--no-build" :: tl, o => parseMutateArgs tl { o with noBuild := true }
  | "--imports" :: v :: tl, o => parseMutateArgs tl { o with extraImports := o.extraImports ++ splitImports v }
  | "--json" :: v :: tl, o => parseMutateArgs tl { o with jsonOut := some ⟨v⟩ }
  | "--min-score" :: v :: tl, o =>
    match parseFloat? v with
    | some f => parseMutateArgs tl { o with minScore := some f }
    | none => throw s!"invalid --min-score value: {v}"
  | "--keep-work" :: tl, o => parseMutateArgs tl { o with keepWork := true }
  | "--" :: tl, o => pure { o with cmdArgs := tl }
  | tok :: tl, o =>
    if tok.startsWith "-" then throw s!"unknown option for mutate: {tok}"
    else pure { o with cmdArgs := tok :: tl }

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

private partial def copyCleanDir (srcDir dstDir skipAbs : System.FilePath) : IO Unit := do
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
  let opts ← match parseMutateArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let rawCmd :: cmdRest := opts.cmdArgs | do
    IO.eprintln "mutate: -- <testCmd> [args...] is required"
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
    let ms ← discoverMutantsInSource env rel src allMutants.size opts.filters
    allMutants := allMutants ++ ms
  let discovered := allMutants.size
  let selected := match opts.maxMutants with
    | some n => (allMutants.take n).mapIdx fun i m => { m with id := i }
    | none => allMutants
  let defaultWork := pkgAbs / ".lake" / "build" / "leancov-mutate"
  let rawWork := opts.workDir.getD defaultWork
  IO.FS.createDirAll rawWork
  let workAbs ← canonicalOrAbs rawWork
  IO.println s!"Staging clean mutation workspace: {pkgAbs} -> {workAbs}"
  IO.println s!"  Target files: {relFiles.size} | Mutants discovered: {discovered} | Running: {selected.size}"
  stageMutateWorkspace pkgAbs workAbs
  let cfg : MutateRunConfig := {
    workDir := workAbs
    buildTargets := opts.buildTargets
    noBuild := opts.noBuild
    testCmd := rawCmd
    testArgs := cmdRest.toArray
    timeoutMs := opts.timeoutMs
  }
  let res ← try
    executeMutants cfg origByFile discovered selected (resolveMutateTestCmd callerCwd pkgAbs workAbs rawCmd)
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
  if let some ms := opts.minScore then
    if rep.score < ms then
      IO.eprintln s!"FAIL: mutation score {rep.score}% < --min-score {ms}%"
      return 1
  return 0

unsafe def runCLI (args : List String) : IO UInt32 := do
  match args with
  | "instrument" :: rest => cmdInstrument rest
  | "stage" :: rest => cmdStage rest
  | "run" :: rest => cmdRun rest
  | "report" :: rest => cmdReport rest
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
