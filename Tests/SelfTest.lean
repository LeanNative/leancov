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

  -- 5. Edge cases of Complexity.walk: `while`, `repeat`, `if let`, `if h :`, `doIf` without `else`,
  -- `doPatDecl` without fallback, `doLetElse` without continuation, `fun` with/without matchAlts,
  -- `declValEqns` with `where` + wildcard tuple, `||` chains, and `by` tactic skipping.
  let edgeCode := "
def orChain (a b c d : Bool) : Bool := a || b || c
def alternatingBool (a b c d : Bool) : Bool := (a && b) || (c && d)

def termIfKinds (xs : Array Nat) (i : Nat) (o : Option Nat) : Nat :=
  if h : i < xs.size then xs[i]
  else if let some v := o then v
  else 0

def loopsAndDoIf (n : Nat) (flag : Bool) (o : Option Nat) : IO Nat := do
  let mut x := n
  while x > 0 do
    x := x - 1
  repeat
    if x == 0 then break
  if flag then
    x := x + 1
  else if n > 10 then
    x := x + 2
  let (a, b) ← pure (x, 1)
  let _ : Nat := by exact 0
  let some v := o | return a + b
  return v

def trailingLetElse (o : Option Nat) : IO Unit := do
  let some _ := o | pure ()

def patLam : Option Nat → Nat := fun
  | some n => n
  | _ => 0

def plainLam : Nat → Nat := fun x => x + 1

def eqnsWithWhere : Option Nat → Option Nat → Nat
  | some a, some b => helper a + b
  | _, _ => 0
where
  helper (k : Nat) : Nat := if k > 0 then k else 1
"
  let r5 ← instrumentSource env "Edge.lean" edgeCode 0 { analyzeOnly := true }
  let needFn (nm : String) : TM FuncInfo :=
    need s!"{nm} found" (match r5.functions.find? (·.name == nm) with | some f => Except.ok f | none => Except.error "missing")
  let fOr ← needFn "orChain"
  checkEq "orChain cognitive" fOr.cognitive 1
  checkEq "orChain CC" fOr.cc 3
  let fAlt ← needFn "alternatingBool"
  checkEq "alternatingBool cognitive" fAlt.cognitive 3
  checkEq "alternatingBool CC" fAlt.cc 4
  let fTermIf ← needFn "termIfKinds"
  checkEq "termIfKinds CC" fTermIf.cc 3
  checkEq "termIfKinds cognitive" fTermIf.cognitive 2
  let fLoops ← needFn "loopsAndDoIf"
  check "loopsAndDoIf CC >= 6" (fLoops.cc ≥ 6)
  check "loopsAndDoIf cognitive >= 6" (fLoops.cognitive ≥ 6)
  let fTrail ← needFn "trailingLetElse"
  checkEq "trailingLetElse CC" fTrail.cc 2
  checkEq "trailingLetElse cognitive" fTrail.cognitive 1
  let fPatLam ← needFn "patLam"
  checkEq "patLam CC" fPatLam.cc 2
  checkEq "patLam cognitive" fPatLam.cognitive 1
  let fPlainLam ← needFn "plainLam"
  checkEq "plainLam CC" fPlainLam.cc 1
  checkEq "plainLam cognitive" fPlainLam.cognitive 0
  let fEqns ← needFn "eqnsWithWhere"
  checkEq "eqnsWithWhere CC (1 non-wildcard arm + where if)" fEqns.cc 3
  checkEq "eqnsWithWhere cognitive (match + outer where if)" fEqns.cognitive 2

  -- 6. Direct synthetic Syntax edge cases for `measureComplexity` (malformed/short/leaf nodes)
  checkEq "measure missing" (measureComplexity .missing) { cc := 1, cognitive := 0 }
  checkEq "measure atom" (measureComplexity (.atom .none "x")) { cc := 1, cognitive := 0 }
  let shortIf := Syntax.node .none `termIfThenElse #[.atom .none "if"]
  checkEq "measure short termIf" (measureComplexity shortIf) { cc := 2, cognitive := 1 }
  let shortDoIf := Syntax.node .none `Lean.Parser.Term.doIf #[.atom .none "if"]
  checkEq "measure short doIf" (measureComplexity shortDoIf) { cc := 2, cognitive := 1 }
  let shortUnless := Syntax.node .none `Lean.Parser.Term.doUnless #[.atom .none "unless"]
  checkEq "measure short doUnless" (measureComplexity shortUnless) { cc := 2, cognitive := 1 }
  let shortCatch := Syntax.node .none `Lean.Parser.Term.doCatch #[]
  checkEq "measure short doCatch" (measureComplexity shortCatch) { cc := 2, cognitive := 1 }
  let shortLetElse := Syntax.node .none `Lean.Parser.Term.doLetElse #[]
  checkEq "measure short doLetElse" (measureComplexity shortLetElse) { cc := 2, cognitive := 1 }
  let shortPatDecl := Syntax.node .none `Lean.Parser.Term.doPatDecl #[]
  checkEq "measure short doPatDecl" (measureComplexity shortPatDecl) { cc := 1, cognitive := 0 }
  let shortAlt := Syntax.node .none `Lean.Parser.Term.matchAlt #[]
  checkEq "measure short matchAlt" (measureComplexity shortAlt) { cc := 1, cognitive := 0 }
  let rawAlt := Syntax.node .none `Lean.Parser.Term.matchAlt
    #[.atom .none "|", .ident .none "x".toRawSubstring `x [], .atom .none "=>", .atom .none "1"]
  checkEq "measure standalone matchAlt" (measureComplexity rawAlt) { cc := 2, cognitive := 0 }
  let shortBool := Syntax.node .none `«term_&&_» #[]
  checkEq "measure short boolOp" (measureComplexity shortBool) { cc := 2, cognitive := 1 }
  let skipInMatch := Syntax.node .none `Lean.Parser.Term.match #[
    .node .none `Lean.Parser.Term.byTactic #[],
    .node .none `Lean.Parser.Term.matchAlts #[rawAlt]
  ]
  checkEq "measure match with skipKind" (measureComplexity skipInMatch) { cc := 2, cognitive := 1 }

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
  let dynExt := if System.Platform.isOSX then "dylib" else if System.Platform.isWindows then "dll" else "so"
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean",
      s!"--load-dynlib=.lake/build/lib/libleancov_rt.{dynExt}",
      s!"--load-dynlib=.lake/build/lib/lean/leancov_LeanCov_Runtime.{dynExt}",
      tmpPath.toString]
  }
  let _ ← IO.Process.output { cmd := "rm", args := #["-f", tmpPath.toString] }
  check "instrumented code typechecks & guards pass" (out.exitCode == 0) s!"{out.stdout}{out.stderr}"

  -- Test `walkCommand` edge cases: multi-part namespaces, named & unnamed sections, `in`, `mutual`,
  -- `instance` (named, anonymous, `where`, pure-const), skipped modifiers, tactic bodies, and parse errors.
  let cmdSample := "
namespace Outer.Inner
section NamedSec
def insideNamed (x : Nat) : Nat := if x > 0 then x else 0
end NamedSec

section
open Nat in
def insideAnonIn (x : Nat) : Nat := if x == 0 then 1 else x
end

mutual
def mutEven : Nat → Bool
  | 0 => true
  | n + 1 => mutOdd n
def mutOdd : Nat → Bool
  | 0 => false
  | n + 1 => mutEven n
end

class Inc (α : Type) where
  inc : α → α

instance namedInc : Inc Nat where
  inc n := if n > 0 then n + 1 else 1

instance : Inc Bool where
  inc b := !b

noncomputable def skipNoncomp (x : Nat) : Nat := x
theorem skipThm : 1 = 1 := rfl
def skipTactic : Nat := by exact 1
def skipProp (n : Nat) : Prop := n = 0

def doShapes (flag : Bool) : Id Nat := do
  let mut acc := 0
  if flag then { acc := acc + 1; acc := acc + 1 }
  if flag then acc := acc + 2
  unless !flag do { acc := acc + 3 }
  unless !flag do acc := acc + 4
  let _ ← if flag then do
    acc := acc + 5
  for x in [1, 2] do { acc := acc + x }
  let mut k := 1
  repeat
    if k == 0 then break
    k := k - 1
  return acc

end Outer.Inner
"
  let cmdRes ← instrumentSource env "CmdEdge.lean" cmdSample 0 {}
  checkEq "cmdSample no skip" cmdRes.skippedReason none
  check "multi-part namespace + named section qualified" (cmdRes.functions.any (·.name == "Outer.Inner.insideNamed"))
  check "unnamed section + open-in qualified" (cmdRes.functions.any (·.name == "Outer.Inner.insideAnonIn"))
  check "mutual def mutEven found" (cmdRes.functions.any (·.name == "Outer.Inner.mutEven"))
  check "mutual def mutOdd found" (cmdRes.functions.any (·.name == "Outer.Inner.mutOdd"))
  check "named instance found" (cmdRes.functions.any (·.name == "Outer.Inner.namedInc"))
  check "noncomputable skipped" (!cmdRes.functions.any (·.name == "Outer.Inner.skipNoncomp"))
  check "theorem skipped" (!cmdRes.functions.any (·.name == "Outer.Inner.skipThm"))
  check "tactic def skipped" (!cmdRes.functions.any (·.name == "Outer.Inner.skipTactic"))
  check "Prop def skipped" (!cmdRes.functions.any (·.name == "Outer.Inner.skipProp"))

  -- Module header & syntax error handling
  let modSrc := "module\npublic def modFn (x : Nat) : Nat := if x > 0 then x else 0\n"
  let modRes ← instrumentSource env "Mod.lean" modSrc 0 {}
  check "module header injects public import" ((modRes.instrumented.splitOn "public import LeanCov.DoSyntax").length > 1)
  let badSrc := "def broken ( := \n"
  let badRes ← instrumentSource env "Bad.lean" badSrc 0 {}
  check "parse error recorded in skippedReason" badRes.skippedReason.isSome
  let badHdr := "import 123invalid\n"
  let badHdrRes ← instrumentSource env "BadHdr.lean" badHdr 0 {}
  check "header parse error recorded" badHdrRes.skippedReason.isSome

  -- Test `armMainInSource` on `declValSimple`, `declValEqns`, `section`/`in`/`_root_.main`, module, and bad syntax
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

  let rootMain := "namespace Foo\nsection S\nopen Nat in\ndef _root_.main : IO Unit := pure ()\nend S\nend Foo\n"
  let (am4, ok4) ← armMainInSource env "RootMain.lean" rootMain
  check "_root_.main inside namespace+section+in IS armed" ok4
  check "_root_.main injects arm" ((am4.splitOn "LeanCov.arm ()").length > 1)

  let modMain := "module\ndef main : IO Unit := pure ()\n"
  let (am5, ok5) ← armMainInSource env "ModMain.lean" modMain
  check "module main armed" ok5
  check "module main injects public import Runtime" ((am5.splitOn "public import LeanCov.Runtime").length > 1)

  let (_, okBad) ← armMainInSource env "BadMain.lean" "def main ( := \n"
  check "armMainInSource syntax error returns false" (!okBad)

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

  -- Empty manifest & high-CRAP / tie-breaker cases
  let emptyRep := buildReport {} #[]
  checkEq "empty report sitesTotal" emptyRep.sitesTotal 0
  checkEq "empty report functionsTotal" emptyRep.functionsTotal 0
  checkEq "empty lcov" (toLcov {} #[]) "\n"
  check "empty formatReport" (((formatReport emptyRep 5 .crap true true true).splitOn "Branches:").length > 1)
  check "empty staticAnalysis" (((formatStaticAnalysis {} 5 true).splitOn "Declarations: 0").length > 1)

  let tieManifest : Manifest := {
    sites := #[
      { id := 0, file := "T.lean", decl := "T.a", line := 1, col := 1, kind := .ifThen },
      { id := 1, file := "T.lean", decl := "T.b", line := 5, col := 1, kind := .ifThen }
    ]
    functions := #[
      { name := "T.b", file := "T.lean", line := 5, endLine := 6, lines := 2, cc := 10, cognitive := 10, siteIds := #[1] },
      { name := "T.a", file := "T.lean", line := 1, endLine := 2, lines := 2, cc := 10, cognitive := 10, siteIds := #[0] },
      { name := "T.empty", file := "OnlyFn.lean", line := 1, endLine := 1, lines := 1, cc := 1, cognitive := 0, siteIds := #[] }
    ]
  }
  let tieRep := buildReport tieManifest #[0, 0]
  checkEq "tieRep crapOver30" tieRep.crapOver30 2
  checkEq "tieRep cogCrapOver30" tieRep.cogCrapOver30 2
  for key in #[SortKey.crap, .cog, .cc, .uncov] do
    let txt := formatReport tieRep 5 key true true true
    check s!"tie formatReport({key.toString})" ((txt.splitOn "T.a").length > 1)
  check "tie lcov includes OnlyFn.lean" (((toLcov tieManifest #[0, 0]).splitOn "SF:OnlyFn.lean").length > 1)

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

  -- Help, version, & invalid subcommand
  checkEq "cli help" (← LeanCov.CLI.runCLI ["--help"]) 0
  checkEq "cli -h" (← LeanCov.CLI.runCLI ["-h"]) 0
  checkEq "cli --version" (← LeanCov.CLI.runCLI ["--version"]) 0
  checkEq "cli -V" (← LeanCov.CLI.runCLI ["-V"]) 0
  checkEq "cli unknown" (← LeanCov.CLI.runCLI ["nope"]) 2
  let cliBin := ((← IO.appPath).parent.getD ".lake/build/bin") / "leancov"
  if ← cliBin.pathExists then
    let vOut ← IO.Process.output { cmd := cliBin.toString, args := #["--version"] }
    checkEq "leancov --version exit 0" vOut.exitCode 0
    checkEq "leancov --version stdout" vOut.stdout.trimAscii.copy s!"leancov {LeanCov.CLI.version}"
    let vShort ← IO.Process.output { cmd := cliBin.toString, args := #["-V"] }
    checkEq "leancov -V exit 0" vShort.exitCode 0
    checkEq "leancov -V stdout" vShort.stdout.trimAscii.copy s!"leancov {LeanCov.CLI.version}"

  -- `analyze`
  let analyzeJson := dir / "analyze.json"
  checkEq "cli analyze cog" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--json", analyzeJson.toString, "--top", "5", "--sort", "cog"]) 0
  checkEq "cli analyze cc" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--exclude", "Nope", "--imports", "Init", "--sort", "cc"]) 0
  checkEq "cli analyze missing src" (← LeanCov.CLI.runCLI ["analyze"]) 2
  checkEq "cli analyze bad top" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--top", "abc"]) 2
  checkEq "cli analyze unknown opt" (← LeanCov.CLI.runCLI ["analyze", "--bogus"]) 2

  -- `instrument`
  let instOut := dir / "inst_out"
  let instSites := dir / "inst_sites.json"
  checkEq "cli instrument" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString, "--out", instOut.toString, "--sites", instSites.toString, "--exclude", "Nope", "--imports", "Init", "--no-bool-ops"]) 0
  check "instrument wrote sites" (← instSites.pathExists)
  let instColonOut := dir / "inst_colon_out"
  checkEq "cli instrument src:out" (← LeanCov.CLI.runCLI ["instrument", "--src", s!"{pkgToml / "Lib"}:{instColonOut}", "--sites", (dir / "inst_colon.json").toString]) 0
  checkEq "cli instrument missing src" (← LeanCov.CLI.runCLI ["instrument", "--sites", instSites.toString]) 2
  checkEq "cli instrument missing sites" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString]) 2
  checkEq "cli instrument missing out" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString, "--sites", instSites.toString]) 2
  checkEq "cli instrument unknown opt" (← LeanCov.CLI.runCLI ["instrument", "--bogus"]) 2

  -- `stage` error paths
  checkEq "cli stage unknown opt" (← LeanCov.CLI.runCLI ["stage", "--bogus"]) 2
  checkEq "cli stage bad --dep" (← LeanCov.CLI.runCLI ["stage", "--dep", "notapair", "--out", (dir / "err1").toString, "--self"]) 2
  checkEq "cli stage empty --dep val" (← LeanCov.CLI.runCLI ["stage", "--dep", "k=", "--out", (dir / "err1").toString, "--self"]) 2
  checkEq "cli stage missing --out" (← LeanCov.CLI.runCLI ["stage", "--pkg", pkgToml.toString, "--self"]) 2
  checkEq "cli stage missing --leancov" (← LeanCov.CLI.runCLI ["stage", "--pkg", pkgToml.toString, "--out", (dir / "err2").toString]) 2

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

  -- `stage` edge cases: `--self`, auto-discovery inside-pkg `--out`, non-Lean symlink dir,
  -- `.lake/packages/*`, top-level excluded `Main.lean`, top-level broken `.lean`, `--imports`, `--no-bool-ops`,
  -- already-present `leancov` require, git dep, and malformed `lake-manifest.json`.
  let pkgSelf := dir / "pkg_self"
  IO.FS.createDirAll (pkgSelf / "Mod")
  IO.FS.createDirAll (pkgSelf / "assets")
  IO.FS.createDirAll (pkgSelf / ".hidden")
  IO.FS.createDirAll (pkgSelf / ".lake" / "packages" / "extpkg")
  IO.FS.writeFile (pkgSelf / "assets" / "note.txt") "hello"
  IO.FS.writeFile (pkgSelf / ".lake" / "packages" / "extpkg" / "README.md") "ext"
  IO.FS.writeFile (pkgSelf / "lakefile.lean")
    "import Lake\nopen Lake DSL\npackage selfpkg\nrequire leancov from \"/abs/leancov\"\nrequire remote from \"https://example.com/repo\"\nrequire ov from \"../ov\"\n"
  IO.FS.writeFile (pkgSelf / "lake-manifest.json") "not valid json"
  IO.FS.writeFile (pkgSelf / "Mod" / "Ok.lean") "def ok (a b : Bool) : Bool := a && b\n"
  IO.FS.writeFile (pkgSelf / "Mod" / "ExcludedMain.lean") "def main : IO Unit := pure ()\n"
  IO.FS.writeFile (pkgSelf / "Mod" / "SubErr.lean") "def subBad ( := \n"
  IO.FS.writeFile (pkgSelf / "Main.lean") "def main : IO Unit := pure ()\n"
  IO.FS.writeFile (pkgSelf / "Broken.lean") "def bad ( := \n"
  let selfStageOut := pkgSelf / "staged_inside"
  checkEq "cli stage --self + edge cases" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgSelf.toString, "--out", selfStageOut.toString,
    "--self", "--dep", s!"ov={pkgLean}", "--exclude", "Main.lean",
    "--imports", "Init", "--no-bool-ops"
  ]) 0
  check "stage --self symlinked assets dir" (← (selfStageOut / "assets" / "note.txt").pathExists)
  check "stage --self symlinked .lake/packages/extpkg" (← (selfStageOut / ".lake" / "packages" / "extpkg" / "README.md").pathExists)
  let selfMainOut ← IO.FS.readFile (selfStageOut / "Main.lean")
  check "stage --self armed excluded top-level Main.lean" ((selfMainOut.splitOn "LeanCov.arm ()").length > 1)
  let exclSubMain ← IO.FS.readFile (selfStageOut / "Mod" / "ExcludedMain.lean")
  check "stage --self armed excluded Mod/ExcludedMain.lean" ((exclSubMain.splitOn "LeanCov.arm ()").length > 1)
  -- Also exercise instrumentTree on an empty directory + excluded file in analyzeOnly mode
  let emptySrc := dir / "empty_src"
  IO.FS.createDirAll emptySrc
  let mEmpty ← instrumentTree emptySrc (dir / "empty_out") {}
  checkEq "instrumentTree empty dir sites" mEmpty.sites.size 0
  let mAnalyzeExcl ← instrumentTree (pkgSelf / "Mod") (pkgSelf / "Mod") { exclude := #["ExcludedMain.lean"], analyzeOnly := true }
  check "instrumentTree analyzeOnly skipped parse error" (!mAnalyzeExcl.skippedFiles.isEmpty)
  let selfLeanOut ← IO.FS.readFile (selfStageOut / "lakefile.lean")
  check "stage --self did not duplicate require leancov" ((selfLeanOut.splitOn "require leancov").length == 2)
  check "stage --self preserved https URL" ((selfLeanOut.splitOn "https://example.com/repo").length > 1)
  -- Also cover `--leancov` equal to `--pkg` (implicit isSelf) and lakefile.toml with existing leancov + abs path
  let pkgSelfToml := dir / "pkg_self_toml"
  IO.FS.createDirAll (pkgSelfToml / "Mod")
  IO.FS.writeFile (pkgSelfToml / "lakefile.toml")
    "name = \"selftoml\"\n[[require]]\nname = \"leancov\"\npath = \"/abs/lc\"\n"
  IO.FS.writeFile (pkgSelfToml / "lake-manifest.json")
    "{\"version\":\"1.3.0\",\"packages\":[{\"type\":\"path\",\"name\":\"leancov\",\"dir\":\"/abs/lc\"},{\"type\":\"git\",\"name\":\"std\"}]}"
  IO.FS.writeFile (pkgSelfToml / "Mod" / "M.lean") "def m (x : Nat) : Nat := x + 1\n"
  checkEq "cli stage --leancov == --pkg" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgSelfToml.toString, "--out", (dir / "stage_self_toml").toString,
    "--leancov", pkgSelfToml.toString
  ]) 0

  -- `run` + `report` (with --files, --kinds, --missed, --json, --lcov, and CI pass/fail gates)
  let prof := dir / "p.cov"
  checkEq "cli run true" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", prof.toString, "--", "true"]) 0
  check "cli run created profile" (← prof.pathExists)
  checkEq "cli run --append" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", prof.toString, "--append", "--no-defer-init", "--", "true"]) 0
  let pidProf := dir / "pid_prof" / "run-%p.cov"
  checkEq "cli run %p profile" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", pidProf.toString, "true"]) 0
  checkEq "cli run missing sites" (← LeanCov.CLI.runCLI ["run", "--profile", prof.toString, "--", "true"]) 2
  checkEq "cli run missing profile" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--", "true"]) 2
  checkEq "cli run missing cmd" (← LeanCov.CLI.runCLI ["run", "--sites", combinedSites.toString, "--profile", prof.toString]) 2
  checkEq "cli run unknown opt" (← LeanCov.CLI.runCLI ["run", "--bogus"]) 2

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
  checkEq "cli report max-cog-crap fail" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--max-cog-crap", "0.5", "--top", "0"
  ]) 1
  checkEq "cli report bad sort" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--sort", "bogus"
  ]) 2
  checkEq "cli report bad top" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--top", "nope"
  ]) 2
  checkEq "cli report bad min-cov" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--min-cov", "nope"
  ]) 2
  checkEq "cli report bad max-crap" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--max-crap", "nope"
  ]) 2
  checkEq "cli report bad max-cog-crap" (← LeanCov.CLI.runCLI [
    "report", "--sites", combinedSites.toString, "--profile", prof.toString, "--max-cog-crap", "nope"
  ]) 2
  checkEq "cli report unknown opt" (← LeanCov.CLI.runCLI ["report", "--bogus"]) 2
  checkEq "cli report missing sites" (← LeanCov.CLI.runCLI ["report", "--profile", prof.toString]) 2
  checkEq "cli report missing profile" (← LeanCov.CLI.runCLI ["report", "--sites", combinedSites.toString]) 2

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

  -- End-to-end `Fuzz.main` supervisor + child + corpus replay + finding + bad option
  let fuzzBin := ((← IO.appPath).parent.getD ".lake/build/bin") / "leancov-fuzz-test"
  if ← fuzzBin.pathExists then
    let fdir : System.FilePath := ".lake/build/tmp_fuzz_e2e"
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", fdir.toString] }
    IO.FS.createDirAll (fdir / "corpus" / "clean")
    IO.FS.writeBinFile (fdir / "corpus" / "clean" / "seed1.bin") "abc".toUTF8
    IO.FS.writeFile (fdir / "corpus" / "clean" / "README.txt") "ignored"
    -- 1. Clean run with corpus replay (and ignored non-.bin file)
    let okOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "clean", "--iterations", "50", "--seed", "0x42", "--max-input", "64"]
      env := #[("LEANCOV_TEST_CORPUS", some (fdir / "corpus").toString)]
    }
    check "fuzz clean + corpus passes" (okOut.exitCode == 0) s!"{okOut.stdout}{okOut.stderr}"
    -- 2. Finding caught & saved (with decimal seed)
    let findOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "finding", "--iterations", "50", "--seed", "66", "--save", (fdir / "saved").toString]
    }
    checkEq "fuzz finding exits 1" findOut.exitCode 1
    check "fuzz finding saved .bin" (← (fdir / "saved" / "finding-0x42.bin").pathExists)
    -- 3. Unparseable seeds exit 1
    let noSeedOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "noseed", "--iterations", "5"]
    }
    checkEq "fuzz noseed exits 1" noSeedOut.exitCode 1
    -- 4. Invalid CLI options exit 2 (fast: checked before spawning child)
    for badArgs in #[#["--bogus"], #["--iterations", "nope"], #["--seed", "0xZZ"], #["--max-input", "abc"]] do
      let badOut ← IO.Process.output { cmd := fuzzBin.toString, args := badArgs }
      checkEq s!"fuzz bad option {badArgs} exits 2" badOut.exitCode 2
    -- 5. Unknown target exits 2
    let unkOut ← IO.Process.output { cmd := fuzzBin.toString, args := #["--target", "doesnotexist", "--iterations", "1"] }
    checkEq "fuzz unknown target exits 2" unkOut.exitCode 2
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", fdir.toString] }

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
