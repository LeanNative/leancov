import Lean.Data.Json
import LeanCov.Check
import LeanCov.Fuzz
import LeanCov.Cov
import LeanCov.CLI

/-! # Comprehensive self-test suite for LeanCov

Covers:
- `Types`: all `BranchKind` JSON/string round-trips, `isBranch`, `.cov` binary validation & merge overflow
- `Complexity`: McCabe CC vs Cognitive Complexity across `match`, nested loops/ifs, `else if`, `&&`/`||`, `let |`, `catch`
- `Instrument`: every Lean control-flow construct, `letPatDecl`, `while ←`, `loop.skip`, bool RHS operands,
  pure CAF exclusion, point-free `fun` entry, `armMainInSource`, `@[never_extract]` exact counts, and typecheck
- `Report`: true branch vs function separation, LCOV `BRDA`/`BRF`/`BRH`, `--kinds`, all sort orders, static analysis
- `CLI`: `analyze`, `instrument`, `stage` (`lakefile.toml` + `lakefile.lean` + `lake-manifest.json` + `--dep`), `run`, `report` + CI gates
- `Fuzz`: SplitMix64, all 10 mutation operators, `require`, `parseOptions` via clean run and error cases -/

open Lean LeanCov.Check LeanCov.Cov

private def catchesIO (act : IO α) : IO Bool :=
  try let _ ← act; pure false catch _ => pure true

private def testTypesAndProfiles : TM Unit := do
  -- All BranchKind string + JSON round-trips
  let allKinds : Array BranchKind := #[
    .ifThen, .ifElse, .unlessEnter, .unlessSkip, .matchArm,
    .letElseOk, .letElseFail, .loopBody, .loopSkip, .catchBody,
    .andTrue, .andFalse, .orTrue, .orFalse, .fnEntry
  ]
  for k in allKinds do
    checkEq s!"ofString {k.toString}" (BranchKind.ofString? k.toString) (some k)
    let j := toJson k
    let back : Except String BranchKind := fromJson? j
    checkEq s!"json roundtrip {k.toString}" back.toOption (some k)
    checkEq s!"isBranch {k.toString}" k.isBranch (k != .fnEntry)
  checkEq "unknown branch kind" (BranchKind.ofString? "bogus") none
  let badJson : Except String BranchKind := fromJson? (Json.str "bogus")
  check "bad json branch kind fails" badJson.toOption.isNone

  -- Binary .cov profile validation error paths & merge saturation
  let dir : System.FilePath := ".lake/build/tmp_types_test"
  IO.FS.createDirAll dir
  let shortF := dir / "short.cov"
  IO.FS.writeBinFile shortF (ByteArray.mk #[1, 2, 3])
  check "rejects short profile" (← catchesIO (readProfile shortF))

  let badMagic := dir / "badmagic.cov"
  IO.FS.writeBinFile badMagic (ByteArray.mk (Array.replicate 24 0))
  check "rejects bad magic" (← catchesIO (readProfile badMagic))

  let truncF := dir / "trunc.cov"
  let mut tb := profileMagic
  -- claim 10 sites, write only 0 bytes of data
  tb := tb ++ ByteArray.mk #[10, 0, 0, 0, 0, 0, 0, 0]
  IO.FS.writeBinFile truncF tb
  check "rejects truncated profile" (← catchesIO (readProfile truncF))

  -- Normal read/write/merge + saturation check
  let mkProf (vals : Array UInt64) : ByteArray := Id.run do
    let mut b := profileMagic
    let pushU64 (acc : ByteArray) (v : UInt64) : ByteArray := Id.run do
      let mut out := acc
      for i in [:8] do out := out.push ((v >>> (i * 8).toUInt64) &&& 0xFF).toUInt8
      return out
    b := pushU64 b vals.size.toUInt64
    for v in vals do b := pushU64 b v
    return b

  let p1 := dir / "p1.cov"
  let p2 := dir / "p2.cov"
  initProfile p1 4
  checkEq "fresh profile zeroed" (← readProfile p1) #[0, 0, 0, 0]
  let maxU64 : UInt64 := 0xFFFF_FFFF_FFFF_FFFF
  IO.FS.writeBinFile p1 (mkProf #[3, 0, maxU64, 1])
  IO.FS.writeBinFile p2 (mkProf #[2, 5, 10, 0])
  let merged ← mergeProfiles #[p1, p2] 4
  checkEq "merge sums & saturates" merged #[5, 5, maxU64, 1]

  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

private unsafe def testComplexity : TM Unit := do
  let env ← loadParserEnv
  -- 1. Flat 8-arm match: high CC (8), Cognitive = 1
  let flatCode := "
def dispatch (k : Nat) : Nat :=
  match k with
  | 0 => 10 | 1 => 11 | 2 => 12 | 3 => 13 | 4 => 14 | 5 => 15 | 6 => 16 | _ => 99
"
  let r1 ← instrumentSource env "Flat.lean" flatCode 0 { analyzeOnly := true }
  checkEq "flat function count" r1.functions.size 1
  checkEq "flat match CC" r1.functions[0]!.cc 8
  checkEq "flat match cognitive" r1.functions[0]!.cognitive 1
  checkEq "flat match probe sites" r1.functions[0]!.siteIds.size 8

  -- 2. Deeply nested control flow: Cognitive (10) > CC (5)
  let nestedCode := "
def nested (xs : List Nat) (flag : Bool) : IO Nat := do
  let mut s := 0
  for x in xs do
    if x > 0 then
      if flag then
        unless x == 5 do
          s := s + x
  return s
"
  let r2 ← instrumentSource env "Nested.lean" nestedCode 0 { analyzeOnly := true }
  checkEq "nested CC" r2.functions[0]!.cc 5
  checkEq "nested cognitive" r2.functions[0]!.cognitive 10

  -- 3. Chained `else if` stays flat in Cognitive Complexity (+1 per else-if)
  let chainCode := "
def grade (n : Nat) : String :=
  if n >= 90 then \"A\"
  else if n >= 80 then \"B\"
  else if n >= 70 then \"C\"
  else \"F\"
"
  let r3 ← instrumentSource env "Chain.lean" chainCode 0 { analyzeOnly := true }
  checkEq "else-if chain CC" r3.functions[0]!.cc 4
  checkEq "else-if chain cognitive" r3.functions[0]!.cognitive 3

  -- 4. Boolean operator transitions + doLetElse + doPatDecl + try/catch
  let boolCode := "
def sameOp (a b c : Bool) : Bool := a && b && c
def mixedOp (a b c : Bool) : Bool := (a && b) || c
def doMix (o : Option Nat) : IO Nat := do
  try
    let some a ← pure o | return 0
    let some b := o | return 1
    if a > 0 then return a
    else if b > 0 then return b
    else return 2
  catch _ =>
    return 3
"
  let r4 ← instrumentSource env "Bool.lean" boolCode 0 { analyzeOnly := true }
  checkEq "sameOp cognitive" r4.functions[0]!.cognitive 1
  checkEq "sameOp CC" r4.functions[0]!.cc 3
  -- 3 atomic operands -> 6 cond sites (and.true + and.false for a, b, c)
  checkEq "sameOp 3 operands -> 6 sites" r4.functions[0]!.siteIds.size 6
  checkEq "mixedOp cognitive" r4.functions[1]!.cognitive 2
  checkEq "mixedOp CC" r4.functions[1]!.cc 3
  checkEq "mixedOp 3 operands -> 6 sites" r4.functions[1]!.siteIds.size 6
  check "doMix CC >= 6" (r4.functions[2]!.cc ≥ 6)

private unsafe def testInstrumentAndRuntimeSemantics : TM Unit := do
  let env ← loadParserEnv
  -- Tricky Lean syntax covering every instrumented construct & all past regressions
  let sample := "
namespace Demo

def pureConst : Nat := 42
def pureTable : Array Nat := #[1, 2, 3]

def straight (x : Nat) : Nat := x + 1

def pointFreeLam : Nat → Nat := fun x => x + 2

def termIf (a b : Bool) (o : Option Nat) : Nat :=
  if a && b then 1
  else if let some v := o then v
  else 0

def depIf (xs : Array Nat) (i : Nat) : Nat :=
  if h : i < xs.size then xs[i] else 0

def structRec : List Nat → Nat
  | [] => 0
  | x :: xs => x + structRec xs
termination_by structural l => l

def letPatMatch (cs : List Char) : Nat := Id.run do
  let (flag, rest) := match cs with
    | '+' :: r => (true, r)
    | '-' :: r => (false, r)
    | r => (true, r)
  return if flag then rest.length else 0

def stateWhileLift (cs : List Char) : StateM (List Char) Nat := do
  let consume (target : Char) : StateM (List Char) Bool := do
    match ← get with
    | c :: rest => if c == target then set rest; return true else return false
    | [] => return false
  let mut count := 0
  while ← consume '/' do
    count := count + 1
  return count

def doKitchenSink (xs : List (Option Nat)) (flag : Bool) : Id Nat := do
  let mut total := 0
  if flag then
    total := total + 1
  unless !flag do
    total := total + 2
  for item in xs do
    let some v := item | continue
    if v == 0 then
      continue
    else if v > 10 then
      total := total + 10
    total := total + v
  return total

def ioCatch (fail : Bool) : IO Nat := do
  try
    let some x ← pure (if fail then none else some 7) | throw (IO.userError \"missing\")
    return x
  catch _ =>
    return 0

structure Box where
  a : Nat
  b : Nat

def multilineStructAndMatch (x : Option Nat) (flag : Bool) : Except String Box := do
  let pfx := if flag then \"foo\" else \"foo\" ++ \"/\"
  let _ := \"foo/bar\".startsWith pfx
  match x with
  | none => throw \"none\"
  | some n => return { a := n,
                       b := n + 1 }

def multilineTermStruct (flag : Bool) : Except String Box :=
  if !flag then .error \"no\"
  else .ok { a := 1,
             b := 2 }

def inferRefUInt64 (xs : List Nat) : IO UInt64 := do
  let rng ← IO.mkRef 0x4C45_414E_434F_5602
  let mut acc : UInt64 := 0
  for x in xs do
    if x > 0 then
      let v : UInt64 ← rng.get
      acc := acc + v
  return acc

inductive Net | main | test
def netCode : Net → UInt32
  | .main => 100
  | .test => 200

end Demo
"
  let res ← instrumentSource env "Demo.lean" sample 0 {}
  checkEq "no parse skip" res.skippedReason none
  -- Pure constants `pureConst` and `pureTable` must be excluded from functions!
  check "pureConst excluded" (!res.functions.any (·.name == "Demo.pureConst"))
  check "pureTable excluded" (!res.functions.any (·.name == "Demo.pureTable"))
  -- Callable functions including `straight` and `pointFreeLam` must be included!
  check "straight included" (res.functions.any (·.name == "Demo.straight"))
  check "pointFreeLam included" (res.functions.any (·.name == "Demo.pointFreeLam"))
  -- `letPatMatch` must have instrumented all 3 match arms inside `let (flag, rest) := match ...`
  let lpm ← need "letPatMatch found" (match res.functions.find? (·.name == "Demo.letPatMatch") with | some f => Except.ok f | none => .error "missing")
  check "letPatMatch has >= 5 sites (3 match arms + if)" (lpm.siteIds.size ≥ 5)
  -- `stateWhileLift` must have both loop.body and loop.skip sites
  let swl ← need "stateWhileLift found" (match res.functions.find? (·.name == "Demo.stateWhileLift") with | some f => Except.ok f | none => .error "missing")
  let swlKinds := swl.siteIds.filterMap fun id => res.sites[id]?.map (·.kind)
  check "stateWhileLift has loop.body" (swlKinds.contains .loopBody)
  check "stateWhileLift has loop.skip" (swlKinds.contains .loopSkip)

  -- Compile the instrumented source with `lake env lean` and verify `stateWhileLift` works semantically!
  let tmpPath : System.FilePath := ".lake/build/tmp_instrument_check.lean"
  if let some p := tmpPath.parent then IO.FS.createDirAll p
  let checkFooter := "
#guard (((Demo.stateWhileLift []).run ['/', '/', 'x']).1 == 2)
#guard (((Demo.stateWhileLift []).run ['x']).1 == 0)
#guard (Demo.letPatMatch ['+', 'a', 'b'] == 2)
#guard (Demo.letPatMatch ['-', 'a'] == 0)
#guard ((Demo.doKitchenSink [some 1, none, some 0, some 12] true).run == 26)
#guard (Demo.netCode .main == 100)
"
  IO.FS.writeFile tmpPath (res.instrumented ++ checkFooter)
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean",
      "--load-dynlib=.lake/build/lib/libleancov_rt.dylib",
      "--load-dynlib=.lake/build/lib/lean/leancov_LeanCov_Runtime.dylib",
      tmpPath.toString]
  }
  let _ ← IO.Process.output { cmd := "rm", args := #["-f", tmpPath.toString] }
  check "instrumented code typechecks & guards pass" (out.exitCode == 0) s!"{out.stdout}{out.stderr}"

  -- Test `armMainInSource` on both `declValSimple` and `declValEqns`
  let m1 := "import Init\ndef main : IO Unit := pure ()\n"
  let (am1, ok1) ← armMainInSource env "M1.lean" m1
  check "armMainInSource simple armed" ok1
  check "armMainInSource injects LeanCov.arm" ((am1.splitOn "LeanCov.arm ()").length > 1)
  check "armMainInSource injects Runtime import" ((am1.splitOn "import LeanCov.Runtime").length > 1)

  let m2 := "def main : List String → IO UInt32\n  | [] => pure 0\n  | _ => pure 1\n"
  let (am2, ok2) ← armMainInSource env "M2.lean" m2
  check "armMainInSource eqns armed" ok2
  check "armMainInSource eqns wraps both arms" ((am2.splitOn "LeanCov.arm ()").length == 3)

  let noMain := "namespace Foo\ndef main : IO Unit := pure ()\nend Foo\n"
  let (_, ok3) ← armMainInSource env "NoMain.lean" noMain
  check "namespaced main is NOT armed" (!ok3)

private def testReportAndLcov : TM Unit := do
  -- Mix real branches AND straight-line `fn.entry` to verify strict branch vs function separation
  let manifest : Manifest := {
    armOnMain := true
    sites := #[
      { id := 0, file := "Foo.lean", decl := "Foo.bar", line := 10, col := 3, kind := .ifThen },
      { id := 1, file := "Foo.lean", decl := "Foo.bar", line := 11, col := 3, kind := .ifElse },
      { id := 2, file := "Foo.lean", decl := "Foo.baz", line := 20, col := 3, kind := .matchArm },
      { id := 3, file := "Foo.lean", decl := "Foo.baz", line := 21, col := 3, kind := .matchArm },
      { id := 4, file := "Foo.lean", decl := "Foo.linear", line := 30, col := 3, kind := .fnEntry }
    ]
    functions := #[
      { name := "Foo.bar", file := "Foo.lean", line := 9, endLine := 12, lines := 4, cc := 2, cognitive := 1, siteIds := #[0, 1] },
      { name := "Foo.baz", file := "Foo.lean", line := 19, endLine := 22, lines := 4, cc := 10, cognitive := 2, siteIds := #[2, 3] },
      { name := "Foo.linear", file := "Foo.lean", line := 30, endLine := 30, lines := 1, cc := 1, cognitive := 0, siteIds := #[4] }
    ]
  }
  let hits : Array UInt64 := #[5, 5, 1, 0, 10]
  let rep := buildReport manifest hits
  -- Branch total must be 4 (excluding site 4 `fn.entry`!), hit must be 3 -> 75.0%
  checkEq "branch sites exclude fn.entry" rep.sitesTotal 4
  checkEq "branch sites hit" rep.sitesHit 3
  -- Functions total = 3 (including Foo.linear), hit = 3
  checkEq "functions total" rep.functionsTotal 3
  checkEq "functions hit" rep.functionsHit 3
  -- Lines total = 5 (includes Foo.linear line 30), hit = 4
  checkEq "lines total" rep.linesTotal 5
  checkEq "lines hit" rep.linesHit 4
  -- CRAP math
  check "Foo.bar CRAP == 2.0" (rep.functions[0]!.crap == 2.0)
  check "Foo.baz CRAP == 22.5" (rep.functions[1]!.crap == 22.5)
  check "Foo.baz CogCRAP == 2.5" (rep.functions[1]!.cogCrap == 2.5)
  check "Foo.linear CRAP == 1.0" (rep.functions[2]!.crap == 1.0)
  checkEq "Foo.baz uncovered line" rep.functions[1]!.uncoveredLines #[21]
  check "byKind populated" (rep.byKind.size == 4)

  -- Verify all sort keys & formatting paths
  for key in #[SortKey.crap, .cog, .cc, .uncov] do
    let txt := formatReport rep 10 key true true true
    check s!"formatReport({key.toString}) has summary" ((txt.splitOn "Branches:").length > 1)
    check s!"formatReport({key.toString}) has kinds" ((txt.splitOn "By branch kind:").length > 1)
    check s!"formatReport({key.toString}) has files" ((txt.splitOn "By file:").length > 1)
    check s!"formatReport({key.toString}) has missed" ((txt.splitOn "missed lines: 21").length > 1)
  checkEq "SortKey.ofString crap" (SortKey.ofString? "crap") (some .crap)
  checkEq "SortKey.ofString cog" (SortKey.ofString? "cog") (some .cog)
  checkEq "SortKey.ofString cc" (SortKey.ofString? "cc") (some .cc)
  checkEq "SortKey.ofString uncov" (SortKey.ofString? "uncov") (some .uncov)
  checkEq "SortKey.ofString bad" (SortKey.ofString? "nope") none

  let statCog := formatStaticAnalysis manifest 10 true
  let statCC := formatStaticAnalysis manifest 10 false
  check "static cog output" ((statCog.splitOn "Static Complexity Analysis").length > 1)
  check "static cc output" ((statCC.splitOn "Foo.baz").length > 1)

  -- LCOV must emit BRF:4 / BRH:3 (excluding fn.entry) and FNF:3 / FNH:3 / LF:5 / LH:4
  let lcov := toLcov manifest hits
  check "LCOV SF" ((lcov.splitOn "SF:Foo.lean").length > 1)
  check "LCOV FNF:3" ((lcov.splitOn "FNF:3").length > 1)
  check "LCOV FNH:3" ((lcov.splitOn "FNH:3").length > 1)
  check "LCOV BRF:4 (excludes fn.entry)" ((lcov.splitOn "BRF:4").length > 1)
  check "LCOV BRH:3" ((lcov.splitOn "BRH:3").length > 1)
  check "LCOV LF:5" ((lcov.splitOn "LF:5").length > 1)
  check "LCOV LH:4" ((lcov.splitOn "LH:4").length > 1)
  check "LCOV end_of_record" ((lcov.splitOn "end_of_record").length > 1)

private unsafe def testCLISubcommands : TM Unit := do
  let dir : System.FilePath := ".lake/build/tmp_cli_test"
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }
  let pkgToml := dir / "pkg_toml"
  let pkgLean := dir / "pkg_lean"
  IO.FS.createDirAll (pkgToml / "Lib")
  IO.FS.createDirAll (pkgToml / "Tests")
  IO.FS.createDirAll (pkgLean / "Src")
  IO.FS.writeFile (pkgToml / "lakefile.toml") "name = \"demo\"\n[[require]]\nname = \"dep\"\npath = \"../dep\"\n"
  IO.FS.writeFile (pkgToml / "lake-manifest.json") "{\"version\":\"1.3.0\",\"packages\":[{\"type\":\"path\",\"name\":\"dep\",\"dir\":\"../dep\"}]}"
  IO.FS.writeFile (pkgToml / "Lib" / "A.lean") "def f (x : Nat) : Nat := if x > 0 then x + 1 else 0\n"
  IO.FS.writeFile (pkgToml / "Tests" / "Main.lean") "def main : IO Unit := pure ()\n"
  IO.FS.writeFile (pkgLean / "lakefile.lean") "import Lake\nopen Lake DSL\npackage foo\nrequire bar from \"../bar\"\n"
  IO.FS.writeFile (pkgLean / "Src" / "B.lean") "def g (a b : Bool) : Bool := a && b\n"
  IO.FS.writeFile (pkgLean / "Main.lean") "def main : IO Unit := pure ()\n"

  -- Help & invalid subcommand
  checkEq "cli help" (← LeanCov.CLI.runCLI ["--help"]) 0
  checkEq "cli unknown" (← LeanCov.CLI.runCLI ["nope"]) 2

  -- `analyze`
  let analyzeJson := dir / "analyze.json"
  checkEq "cli analyze cog" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--json", analyzeJson.toString, "--top", "5", "--sort", "cog"]) 0
  checkEq "cli analyze cc" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--sort", "cc"]) 0
  checkEq "cli analyze missing src" (← LeanCov.CLI.runCLI ["analyze"]) 2

  -- `instrument`
  let instOut := dir / "inst_out"
  let instSites := dir / "inst_sites.json"
  checkEq "cli instrument" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString, "--out", instOut.toString, "--sites", instSites.toString, "--no-bool-ops"]) 0
  check "instrument wrote sites" (← instSites.pathExists)
  checkEq "cli instrument missing sites" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString]) 2

  -- `stage` on lakefile.toml + lake-manifest.json + --dep + --prefix, then --append-sites on lakefile.lean!
  let stage1 := dir / "stage1"
  let stage2 := dir / "stage2"
  let combinedSites := dir / "combined_sites.json"
  checkEq "cli stage toml" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgToml.toString, "--out", stage1.toString, "--leancov", ".",
    "--src-dir", "Lib", "--prefix", "Pkg1", "--dep", s!"dep={pkgLean}",
    "--sites", combinedSites.toString, "--exclude", "Tests/"
  ]) 0
  let tomlOut ← IO.FS.readFile (stage1 / "lakefile.toml")
  check "stage toml added leancov" ((tomlOut.splitOn "name = \"leancov\"").length > 1)
  check "stage toml overrode dep" ((tomlOut.splitOn "pkg_lean").length > 1)
  let mainOut ← IO.FS.readFile (stage1 / "Tests" / "Main.lean")
  check "stage armed Tests/Main.lean" ((mainOut.splitOn "LeanCov.arm ()").length > 1)

  checkEq "cli stage lean + append-sites" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgLean.toString, "--out", stage2.toString, "--leancov", ".",
    "--prefix", "Pkg2", "--sites", combinedSites.toString, "--append-sites"
  ]) 0
  let leanOut ← IO.FS.readFile (stage2 / "lakefile.lean")
  check "stage lean added leancov" ((leanOut.splitOn "require leancov from").length > 1)

  -- `run` + `report` (with --files, --kinds, --missed, --json, --lcov, and CI pass/fail gates)
  let prof := dir / "p.cov"
  checkEq "cli run /usr/bin/true" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", prof.toString, "--", "/usr/bin/true"]) 0
  check "cli run created profile" (← prof.pathExists)
  checkEq "cli run --append" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", prof.toString, "--append", "--no-defer-init", "--", "/usr/bin/true"]) 0
  let repJson := dir / "rep.json"
  let repLcov := dir / "rep.info"
  checkEq "cli report ok" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile-dir", dir.toString,
    "--files", "--kinds", "--missed", "--sort", "cog", "--top", "10",
    "--json", repJson.toString, "--lcov", repLcov.toString
  ]) 0
  checkEq "cli report min-cov fail" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--min-cov", "50.0", "--top", "0"
  ]) 1
  checkEq "cli report max-crap fail" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--max-crap", "0.5", "--top", "0"
  ]) 1
  checkEq "cli report bad sort" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--sort", "bogus"
  ]) 2

  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

private def testFuzzPrimitives : TM Unit := do
  let r1 ← IO.mkRef (0x12345678 : UInt64)
  let r2 ← IO.mkRef (0x12345678 : UInt64)
  checkEq "next deterministic" (← LeanCov.Fuzz.next r1) (← LeanCov.Fuzz.next r2)
  checkEq "index 0 bound" (← LeanCov.Fuzz.index r1 0) 0
  -- Exercise all 10 mutation operators (with and without tokens, empty and non-empty)
  let toks := #["abc".toUTF8, "123".toUTF8]
  for i in [:40] do
    let base := if i % 5 == 0 then ByteArray.empty else "hello world 12345".toUTF8
    let m ← LeanCov.Fuzz.mutate base r1 32 (if i % 2 == 0 then toks else #[])
    check "mutate respects max" (m.size ≤ 32)
  -- `require` pass & fail
  LeanCov.Fuzz.require true "ok"
  check "Fuzz.require throws on false" (← catchesIO (LeanCov.Fuzz.require false "boom"))

/-- End-to-end ground-truth verification: stage, build, and execute a real binary, then assert
EXACT per-site hit counts in the binary `.cov` file for:
1. zero startup hits from a CAF calling an instrumented helper (`LEAN_COV_DEFER_INIT=1`),
2. exact multi-hit counts on constant-returning `match` arms (`@[never_extract]`),
3. exact `loop.body` & `loop.skip` counts on `for` and `while ←` in `StateM`,
4. exact `&&` LHS & RHS operand outcomes (catching untested `b = false`),
5. exact `let (a, b) := match ...` arm hits, and
6. pure CAF exclusion + straight-line `fn.entry` separation. -/
private unsafe def testExactRuntimeCounters : TM Unit := do
  let dir : System.FilePath := ".lake/build/tmp_exact_rt"
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }
  let pkg := dir / "pkg"
  let stage := dir / "stage"
  IO.FS.createDirAll (pkg / "Exact")
  IO.FS.writeFile (pkg / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
  IO.FS.writeFile (pkg / "lakefile.toml")
    "name = \"exact\"\ndefaultTargets = [\"exact-bin\"]\n[[lean_lib]]\nname = \"Exact\"\n[[lean_exe]]\nname = \"exact-bin\"\nroot = \"Main\"\n"
  IO.FS.writeFile (pkg / "Exact.lean") "import Exact.Lib\n"
  IO.FS.writeFile (pkg / "Exact" / "Lib.lean") "namespace Exact

def initOnlyHelper (n : Nat) : Nat :=
  if n > 0 then n + 1 else 0

-- Top-level CAF calls `initOnlyHelper` during module init (BEFORE `main` runs!)
def initTable : Nat := initOnlyHelper 5

inductive Tag | a | b
def tagCode : Tag → UInt32
  | .a => 10
  | .b => 20

def sumList (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

def countLeadingSlashes (cs : List Char) : Nat :=
  (go.run cs).1
where
  consume : StateM (List Char) Bool := do
    match ← get with
    | '/' :: rest => set rest; return true
    | _ => return false
  go : StateM (List Char) Nat := do
    let mut n := 0
    while ← consume do
      n := n + 1
    return n

def bothTrue (a b : Bool) : Bool := a && b

def splitSign (cs : List Char) : Nat := Id.run do
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  return if neg then 0 else rest.length

def linear (x : Nat) : Nat := x + 1

end Exact
"
  IO.FS.writeFile (pkg / "Main.lean") "import Exact
open Exact

def main : IO Unit := do
  -- Touch `initTable` (already computed at init; must NOT credit `initOnlyHelper`!)
  let t0 := initTable
  -- Call `tagCode` 7 times with runtime array elements (so CSE cannot hoist out of loop)
  let tags : Array Tag := Array.replicate 7 .a
  let mut acc : UInt32 := 0
  for t in tags do acc := acc + tagCode t
  -- `sumList`: once empty (loop.skip = 1), twice with 3 items (loop.body = 6)
  let s1 := sumList [] + sumList [1, 2, 3] + sumList [4, 5, 6]
  -- `countLeadingSlashes`: once 0 slashes (loop.skip = 1), once 2 slashes (loop.body = 2)
  let s2 := countLeadingSlashes ['x'] + countLeadingSlashes ['/', '/', 'x']
  -- `bothTrue`: (true, true) and (false, true) -> b=false is NEVER hit!
  let b1 := bothTrue true true
  let b2 := bothTrue false true
  -- `splitSign`: hit only the non-`-` arm
  let s3 := splitSign ['a', 'b']
  -- `linear`: called once
  let s4 := linear 10
  if t0 != 6 || acc != 70 || s1 != 21 || s2 != 2 || !b1 || b2 || s3 != 2 || s4 != 11 then
    throw (IO.userError \"unexpected result\")
"
  let sitesPath := stage / "sites.json"
  let profPath := stage / "run.cov"
  checkEq "stage exact pkg" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkg.toString, "--out", stage.toString, "--leancov", ".",
    "--src-dir", "Exact", "--sites", sitesPath.toString, "--exclude", "Main.lean"
  ]) 0
  let buildOut ← IO.Process.output { cmd := "lake", args := #["build", "exact-bin"], cwd := some stage }
  check "exact-bin built" (buildOut.exitCode == 0) s!"{buildOut.stdout}{buildOut.stderr}"
  checkEq "exact-bin run" (← LeanCov.CLI.runCLI [
    "run", "--sites", sitesPath.toString, "--profile", profPath.toString, "--",
    (stage / ".lake" / "build" / "bin" / "exact-bin").toString
  ]) 0

  let raw ← IO.FS.readFile sitesPath
  let manifest ← needE "parse exact sites.json" id (Json.parse raw >>= fromJson? : Except String Manifest)
  let hits ← readProfile profPath
  check "manifest.armOnMain is true" manifest.armOnMain

  let fnCounts (name : String) : Array (BranchKind × UInt64) :=
    match manifest.functions.find? (·.name == name) with
    | none => #[]
    | some f => f.siteIds.filterMap fun id =>
      manifest.sites[id]?.map fun s => (s.kind, hits[id]!)

  -- 1. Pure CAF `initTable` excluded; `initOnlyHelper` called ONLY during module init -> 0 hits!
  check "initTable excluded" (!manifest.functions.any (·.name == "Exact.initTable"))
  let initHelper := fnCounts "Exact.initOnlyHelper"
  checkEq "initOnlyHelper has 2 sites" initHelper.size 2
  check "initOnlyHelper 0 startup hits" (initHelper.all (·.2 == 0))

  -- 2. `@[never_extract]`: `tagCode .a` counted 7 times (not capped at 1, not blinded to 0!)
  let tc := fnCounts "Exact.tagCode"
  checkEq "tagCode exact counts" (tc.map (·.2)) #[7, 0]

  -- 3. `sumList`: loop.body = 6, loop.skip = 1
  let sl := fnCounts "Exact.sumList"
  let slBody := (sl.find? (·.1 == .loopBody)).map (·.2)
  let slSkip := (sl.find? (·.1 == .loopSkip)).map (·.2)
  checkEq "sumList loop.body == 6" slBody (some 6)
  checkEq "sumList loop.skip == 1" slSkip (some 1)

  -- 4. `countLeadingSlashes` (`while ←` in `StateM`): loop.body = 2, loop.skip = 1
  let cls := fnCounts "Exact.countLeadingSlashes"
  let clsBody := (cls.find? (·.1 == .loopBody)).map (·.2)
  let clsSkip := (cls.find? (·.1 == .loopSkip)).map (·.2)
  checkEq "while<- loop.body == 2" clsBody (some 2)
  checkEq "while<- loop.skip == 1" clsSkip (some 1)

  -- 5. `bothTrue`: a.true=1, a.false=1, b.true=1, b.false=0 (NOT 100%!)
  let bt := fnCounts "Exact.bothTrue"
  checkEq "bothTrue 4 operand sites" bt.size 4
  checkEq "bothTrue exact counts" (bt.map (·.2)) #[1, 1, 1, 0]

  -- 6. `splitSign`: letPatDecl arms hit [0, 1]
  let ss := fnCounts "Exact.splitSign"
  let ssArms := ss.filter (·.1 == .matchArm) |>.map (·.2)
  checkEq "splitSign letPatDecl arm counts" ssArms #[0, 1]

  -- 7. `linear`: fn.entry hit once, excluded from SummaryReport.sitesTotal
  let lin := fnCounts "Exact.linear"
  checkEq "linear fn.entry == 1" (lin.map (·.2)) #[1]
  let rep := buildReport manifest hits
  let expectedBrTot := manifest.sites.filter (·.kind.isBranch) |>.size
  checkEq "SummaryReport.sitesTotal excludes fn.entry" rep.sitesTotal expectedBrTot

  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

unsafe def main : IO UInt32 :=
  runMain "leancov-test" do
    runTest "types & binary profiles" testTypesAndProfiles
    runTest "complexity (CC vs Cognitive)" testComplexity
    runTest "AST instrumentation, runtime semantics & armMain" testInstrumentAndRuntimeSemantics
    runTest "report, kinds & LCOV" testReportAndLcov
    runTest "CLI subcommands end-to-end" testCLISubcommands
    runTest "fuzz primitives & mutator" testFuzzPrimitives
    runTest "exact binary runtime counters (ground truth)" testExactRuntimeCounters
