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
  let pZero := dir / "p0.cov"
  initProfile pZero 0
  checkEq "0-site profile read" (← readProfile pZero) #[]
  checkEq "empty mergeProfiles" (← mergeProfiles #[] 0) #[]
  let wp := dir / "written.cov"
  writeProfile wp #[7, 0, 42]
  checkEq "writeProfile round-trip" (← readProfile wp) #[7, 0, 42]

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
  constTag : Nat := 0
  inc : α → α
  ping : IO Unit := pure ()

instance namedInc : Inc Nat where
  inc n := if n > 0 then n + 1 else 1

instance : Inc Bool where
  constTag := 7
  inc b := !b

instance lamAndDoInc : Inc Int where
  constTag := 9
  inc := fun x => x + 1
  ping := do
    pure ()

class PureConstCls (α : Type) where
  tag : Nat

instance pureOnlyInst : PureConstCls Nat where
  tag := 42

noncomputable def skipNoncomp (x : Nat) : Nat := x
theorem skipThm : 1 = 1 := rfl
def skipTactic : Nat := by exact 1
def skipProp (n : Nat) : Prop := n = 0
def skipTypeAlias : Type := Nat
def skipSortAlias : Sort 1 := Prop
def unannotatedTypeAlias (α : Type) := α
meta def skipMeta (x : Nat) : Nat := x
unsafe def skipUnsafe (x : Nat) : Nat := x

def richBinders {α : Type} ⦃_β : Type⦄ [Inhabited α] (x : Nat) (o : Option Nat) : Nat :=
  let _n := `foo
  let _m := ``Nat
  if x == 0 then 1 else if let some v := o then v else
  suffices _h : x = x from (if x > 0 then x else 0 : Nat)
  rfl

def funMatchFn : Nat → Nat := fun
  | 0 => 1
  | n => n

def _root_.topRootFn (x : Nat) : Nat := if x > 0 then x else 1

instance eqnsWhereInst : Inc UInt8 where
  inc
    | 0 => 1
    | n => helper n
where
  helper (k : UInt8) : UInt8 := k + 1

def doDepAndPat (x : Nat) : IO Nat := do
  if _h : x > 0 && x < 10 then
    let (a, b) ← pure (x, 1)
    return a + b
  let (c, _) ← pure (0, 1) | return 99
  return c

def doShapes (flag : Bool) : Id Nat := do
  let mut acc := 0
  if flag then {
    acc := acc + 1
  }
  if flag then { acc := acc + 1; acc := acc + 1 }
  if flag then acc := acc + 2
  if let some v := (some 1 : Option Nat) then if flag then
    acc := acc + v
  if flag then acc := acc + 3
               acc := acc + 4
  if !flag then { acc := acc + 1 } else if flag then
    acc := acc + 5
    acc := acc + 6
  if !flag then { acc := acc + 1 } else if flag then acc := acc + 5
                                                     acc := acc + 6
  unless !flag do {
    acc := acc + 2
  }
  unless !flag do { acc := acc + 3 }
  unless !flag do acc := acc + 4
  unless !flag do if flag then acc := acc + 1
  unless !flag do acc := acc + 7
                  acc := acc + 8
  match acc with
  | 0 => unless !flag do acc := acc + 1
  | 1 => { acc := acc + 2 }
  | _ => pure ()
  if flag then acc := 1 else acc := 2
                             acc := 3
  if (flag &&
      (acc == 0 || acc > 0)) then
    for x in [1, 2] do acc := acc + x
  if flag then for x in [1, 2] do acc := acc + x
  for x in [1, 2] do acc := acc + x
                     acc := acc + 1
  for x in [1, 2] do { acc := acc + x }
  let mut k := 1
  repeat
    if k == 0 then break
    k := k - 1
  return match flag with
    | true =>
      acc +
      1
    | false => acc

end Outer.Inner
"
  let cmdRes ← instrumentSource env "CmdEdge.lean" cmdSample 0 {}
  checkEq "cmdSample no skip" cmdRes.skippedReason none
  check "multi-part namespace + named section qualified" (cmdRes.functions.any (·.name == "Outer.Inner.insideNamed"))
  check "unnamed section + open-in qualified" (cmdRes.functions.any (·.name == "Outer.Inner.insideAnonIn"))
  check "mutual def mutEven found" (cmdRes.functions.any (·.name == "Outer.Inner.mutEven"))
  check "mutual def mutOdd found" (cmdRes.functions.any (·.name == "Outer.Inner.mutOdd"))
  check "named instance found" (cmdRes.functions.any (·.name == "Outer.Inner.namedInc"))
  -- Callable 0-branch `instance ... where` fields get `.fnEntry` probes while pure constant fields do not!
  let anonBoolInst ← need "anon Inc Bool instance found"
    (match cmdRes.functions.find? (fun f => (f.name.splitOn "(instance").length > 1) with
     | some f => Except.ok f | none => Except.error "missing")
  checkEq "anon Inc Bool has 1 fn.entry probe (skips constTag)" anonBoolInst.siteIds.size 1
  let lamDoInst ← need "lamAndDoInc instance found"
    (match cmdRes.functions.find? (·.name == "Outer.Inner.lamAndDoInc") with
     | some f => Except.ok f | none => Except.error "missing")
  checkEq "lamAndDoInc has 2 fn.entry probes (fun + do, skips constTag)" lamDoInst.siteIds.size 2
  check "pure-constant-only instance excluded" (!cmdRes.functions.any (·.name == "Outer.Inner.pureOnlyInst"))
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

  -- Resilient per-command parsing + module-namespace `def main` arming + single-pass `armMains`
  let partialErrSrc := "namespace App.Runner\ndef helper (x : Nat) : IO UInt32 := if x > 0 then pure 0 else pure 1\nmeta def badQuot : Unit := `(UnknownSyntaxCat| foo)\ndef afterErr (x : Nat) : IO UInt32 := if x == 0 then pure 1 else pure 0\ndef main : IO UInt32 := do\n  let _ ← helper 1\n  afterErr 1\nend App.Runner\n"
  let pRes ← instrumentSource env "Pkg/App/Runner.lean" partialErrSrc 0 { armMains := true }
  checkEq "partial command error does not skip whole file" pRes.skippedReason none
  check "valid helper before custom syntax is instrumented" (pRes.functions.any (·.name == "App.Runner.helper"))
  check "valid def after custom syntax is instrumented" (pRes.functions.any (·.name == "App.Runner.afterErr"))
  check "module-namespaced main armed in single pass" pRes.armedMain
  check "module-namespaced main has LeanCov.arm" ((pRes.instrumented.splitOn "LeanCov.arm ()").length > 1)

  let mutMainSrc := "import LeanCov.Runtime\nmutual\ndef main : IO Unit := do\n  pure ()\nend\n"
  let (amMut, okMut) ← armMainInSource env "MutMain.lean" mutMainSrc
  check "mutual main armed" okMut
  check "existing Runtime import not duplicated" ((amMut.splitOn "import LeanCov.Runtime").length == 2)

  -- Overlapping splice events (`SpliceEvent.lt`): same-byte open+open (diff & equal spanEnd), close+close, open+replace
  let spliceSrc := "def overlap (x : Nat) (a b : Bool) : Bool := match x with | 0 => a && b | _ => false\ndef tabFn (flag : Bool) : Id Nat := do\n\tif flag then\n\t\treturn 1\n\treturn 0\ndef main (n : Nat) : IO UInt32 := pure 0\n"
  let spRes ← instrumentSource env "Splice.lean" spliceSrc 0 { armMains := true }
  check "overlap + parameterized main armed & instrumented" (spRes.armedMain && spRes.sites.size ≥ 5)

  -- Pure 0-probe `main` files under `instrumentSource { armMains := true }` & `armMainInSource` variants
  let pureMainNoHdr ← instrumentSource env "PureMain0.lean" "def main : IO Unit := pure ()\n" 0 { armMains := true }
  check "pure main hdrEnd=0 armed" (pureMainNoHdr.armedMain && (pureMainNoHdr.instrumented.splitOn "import LeanCov.Runtime").length > 1)
  let pureMainDoStx ← instrumentSource env "PureMain1.lean" "import LeanCov.DoSyntax\ndef main : IO Unit := pure ()\n" 0 { armMains := true }
  check "pure main with DoSyntax armed without extra Runtime" pureMainDoStx.armedMain
  let pureMainRt ← instrumentSource env "PureMain2.lean" "import LeanCov.Runtime\ndef main : IO Unit := pure ()\n" 0 { armMains := true }
  check "pure main with Runtime armed" pureMainRt.armedMain
  let (_, okCommentMain) ← armMainInSource env "CommentMain.lean" "-- mentions main in comment\ndef foo : Nat := 1\n"
  check "comment mentioning main is not armed" (!okCommentMain)
  let (amDoStx, okDoStx) ← armMainInSource env "DoStxMain.lean" "import LeanCov.DoSyntax\ndef main : IO Unit := pure ()\n"
  check "armMainInSource with existing DoSyntax import" (okDoStx && (amDoStx.splitOn "import LeanCov.Runtime").length == 1)

  -- Direct `resolveSysroot` checks (env override, project dir, and standalone `/tmp` elan fallback)
  let srCustom ← resolveSysroot none (some "/custom/lean/sysroot")
  checkEq "resolveSysroot honors env override" srCustom ⟨"/custom/lean/sysroot"⟩
  let srHere ← resolveSysroot (some ⟨"."⟩) (some "")
  check "resolveSysroot from project dir non-empty" (!srHere.toString.isEmpty)
  let srStandalone ← resolveSysroot (some ⟨"/tmp"⟩) (some "")
  check "resolveSysroot standalone fallback non-empty" (!srStandalone.toString.isEmpty)

  -- `-- leancov:ignore` single-line, block start/end, and non-comment string safety
  let ignSrc := "
def ignDemo (x : Nat) (b : Bool) : IO Nat := do
  let s := \"-- leancov:ignore\"
  if s.length > 0 then
    pure ()
  if x > 99 then -- leancov:ignore
    pure () -- leancov:ignore
  else
    pure ()
  -- leancov:ignore-start
  unless b do
    for _ in [1, 2] do
      pure ()
  -- leancov:ignore-end
  if b && !b then
    return 1
  return 0

-- leancov:ignore-start
def ignAllFunc (n : Nat) : Nat := n + 1
-- leancov:ignore-end

def oneArmedIgnore (b : Bool) (n : Nat) : IO Unit := do
  if b then -- leancov:ignore
    IO.println n -- leancov:ignore
  if b then
    IO.println n -- leancov:ignore
  if b then {
    IO.println n
  }
  if b then do
    IO.println n
    IO.println (n + 1)
  else if n > 0 then
    IO.println n
"
  let ignRes ← instrumentSource env "IgnoreDemo.lean" ignSrc 0 {}
  checkEq "ignDemo parses cleanly after ignores" ignRes.skippedReason none
  check "ignAllFunc skipped when body ignored" (!ignRes.functions.any (·.name == "ignAllFunc"))
  let _ ← need "ignDemo present"
    (match ignRes.functions.find? (·.name == "ignDemo") with
     | some f => Except.ok f | none => Except.error "missing")
  check "ignDemo skipped unless/for inside ignore block"
    (!ignRes.sites.any (fun s => s.decl == "ignDemo" && (s.kind == .unlessEnter || s.kind == .loopBody)))
  check "ignDemo kept non-ignored bool ops"
    (ignRes.sites.any (fun s => s.decl == "ignDemo" && s.kind == .andTrue))

  -- Smart `loop.skip` suppression: non-empty literals omit `loop.skip`, empty/dynamic keep `loop.skip`
  let loopSkipSrc := "
def staticLoops (seed : Nat) : Nat := Id.run do
  let mut s := seed
  for i in [0:16] do s := s + i
  for i in [:8] do s := s + i
  for i in [1:5:2] do s := s + i
  for i in [:8:2] do s := s + i
  for x in [1, 2] do s := s + x
  for x in #[1, 2] do s := s + x
  for i in [0:4], x in [1] do s := s + i + x
  return s

def dynamicAndEmptyLoops (n : Nat) (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for i in [5:5] do s := s + i
  for i in [:0] do s := s + i
  for i in [0:4:0] do s := s + i
  for i in [:8:0] do s := s + i
  for i in [1:5:0] do s := s + i
  for i in [:n] do s := s + i
  for i in [0:n] do s := s + i
  for i in [n:8] do s := s + i
  for i in [:8:n] do s := s + i
  for i in [1:5:n] do s := s + i
  for x in ([] : List Nat) do s := s + x
  for x in (#[] : Array Nat) do s := s + x
  for x in xs do s := s + x
  for i in [0:4], x in xs do s := s + i + x
  return s
"
  let loopRes ← instrumentSource env "LoopSkip.lean" loopSkipSrc 0 {}
  checkEq "loopSkipSrc parses cleanly" loopRes.skippedReason none
  let staticSites := loopRes.sites.filter (·.decl == "staticLoops")
  checkEq "staticLoops has 7 loop.body sites" (staticSites.countP (·.kind == .loopBody)) 7
  checkEq "staticLoops has 0 loop.skip sites" (staticSites.countP (·.kind == .loopSkip)) 0
  let dynSites := loopRes.sites.filter (·.decl == "dynamicAndEmptyLoops")
  checkEq "dynamicAndEmptyLoops has 14 loop.body sites" (dynSites.countP (·.kind == .loopBody)) 14
  checkEq "dynamicAndEmptyLoops has 14 loop.skip sites" (dynSites.countP (·.kind == .loopSkip)) 14

  -- Pure 0-arg CAF exclusion (including `Id.run do` tables) vs callable 0-arg monads/arrows/callbacks
  let cafSrc := "
structure CbBox where
  f : Bool → Nat

def unannotCaf := 123

def idRunTable : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [:4] do
    b := b.push i.toUInt8
  return b

def matchCaf : Nat :=
  match (some 1 : Option Nat) with
  | some v => v
  | none => 0

def ioAct : IO Nat := do
  return 1

def customM : Id Nat := do
  if true then return 1 else return 2

def arrowFn : Nat → Nat :=
  let k := 1
  fun x => if x > k then x + k else 0

def asciiArrowFn : Nat -> Nat :=
  let k := 2
  fun x => if x > k then x else 0

def cbHolder : CbBox :=
  { f := fun x => if x then 1 else 0 }
"
  let cafDefault ← instrumentSource env "Caf.lean" cafSrc 0 {}
  check "unannotCaf excluded by default" (!cafDefault.functions.any (·.name == "unannotCaf"))
  check "idRunTable CAF excluded by default" (!cafDefault.functions.any (·.name == "idRunTable"))
  check "matchCaf CAF excluded by default" (!cafDefault.functions.any (·.name == "matchCaf"))
  check "ioAct remains instrumented" (cafDefault.functions.any (·.name == "ioAct"))
  check "customM remains instrumented" (cafDefault.functions.any (·.name == "customM"))
  check "arrowFn remains instrumented" (cafDefault.functions.any (·.name == "arrowFn"))
  check "asciiArrowFn remains instrumented" (cafDefault.functions.any (·.name == "asciiArrowFn"))
  check "cbHolder remains instrumented" (cafDefault.functions.any (·.name == "cbHolder"))
  let cafIncluded ← instrumentSource env "Caf.lean" cafSrc 0 { includeCafs := true }
  check "idRunTable included when includeCafs=true" (cafIncluded.functions.any (·.name == "idRunTable"))
  check "matchCaf included when includeCafs=true" (cafIncluded.functions.any (·.name == "matchCaf"))

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
  for key in #[SortKey.crap, .cog, .cc, .uncov, .cov] do
    let txt := formatReport rep 10 key true true true
    check s!"formatReport({key.toString}) has summary" ((txt.splitOn "Branches:").length > 1)
    check s!"formatReport({key.toString}) has kinds" ((txt.splitOn "By branch kind:").length > 1)
    check s!"formatReport({key.toString}) has files" ((txt.splitOn "By file:").length > 1)
    check s!"formatReport({key.toString}) has missed" ((txt.splitOn "missed lines: 21").length > 1)
  checkEq "SortKey.ofString crap" (SortKey.ofString? "crap") (some .crap)
  checkEq "SortKey.ofString cog" (SortKey.ofString? "cog") (some .cog)
  checkEq "SortKey.ofString cc" (SortKey.ofString? "cc") (some .cc)
  checkEq "SortKey.ofString uncov" (SortKey.ofString? "uncov") (some .uncov)
  checkEq "SortKey.ofString cov" (SortKey.ofString? "cov") (some .cov)
  checkEq "SortKey.ofString low" (SortKey.ofString? "low") (some .cov)
  checkEq "SortKey.ofString bad" (SortKey.ofString? "nope") none
  let covSorted := sortFuncReports rep.functions .cov
  checkEq "SortKey.cov puts lowest branchCov first" covSorted[0]!.name "Foo.baz"

  -- ReportFilter & filterManifest (--file, --decl, --exclude-kind) + HTML escape/filenames
  let fltManifest : Manifest := {
    sites := #[
      { id := 0, file := "Alpha/A.lean", decl := "Alpha.f1", line := 5, col := 3, kind := .ifThen },
      { id := 1, file := "Alpha/A.lean", decl := "Alpha.f1", line := 6, col := 3, kind := .loopSkip },
      { id := 2, file := "Beta/B.lean", decl := "Beta.f2", line := 10, col := 3, kind := .loopSkip }
    ]
    functions := #[
      { name := "Alpha.f1", file := "Alpha/A.lean", line := 4, endLine := 7, lines := 4, cc := 2, cognitive := 1, siteIds := #[0, 1] },
      { name := "Beta.f2", file := "Beta/B.lean", line := 9, endLine := 12, lines := 4, cc := 2, cognitive := 1, siteIds := #[2] }
    ]
  }
  checkEq "filterManifest empty is identity" (filterManifest fltManifest {}).sites.size 3
  let fltByFile := filterManifest fltManifest { files := #["Alpha"] }
  checkEq "filterManifest --file keeps Alpha sites" fltByFile.sites.size 2
  checkEq "filterManifest --file keeps Alpha func" fltByFile.functions.size 1
  let fltNoSkip := filterManifest fltManifest { excludeKinds := #[.loopSkip] }
  checkEq "filterManifest --exclude-kind loop.skip keeps site 0" fltNoSkip.sites.size 1
  checkEq "filterManifest preserves original Site.id" fltNoSkip.sites[0]!.id 0
  checkEq "filterManifest drops Beta.f2 when all its sites excluded" fltNoSkip.functions.size 1
  let fltEmpty := filterManifest fltManifest { decls := #["MissingDecl"] }
  checkEq "filterManifest non-matching decl yields 0" fltEmpty.functions.size 0

  checkEq "htmlEscape" (htmlEscape "<a & \"b\" 'c'>") "&lt;a &amp; &quot;b&quot; &#39;c&#39;&gt;"
  checkEq "safeHtmlFileName" (safeHtmlFileName "Winnow/Sha2.lean") "Winnow__Sha2.lean.html"

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
  let shortHitsRep := buildReport manifest #[]
  checkEq "short hits array treated as 0 hits" shortHitsRep.sitesHit 0
  let emptyRep := buildReport {} #[]
  checkEq "empty report sitesTotal" emptyRep.sitesTotal 0
  checkEq "empty report functionsTotal" emptyRep.functionsTotal 0
  checkEq "empty lcov" (toLcov {} #[]) "\n"
  check "empty formatReport" (((formatReport emptyRep 5 .crap true true true).splitOn "Branches:").length > 1)
  check "empty staticAnalysis" (((formatStaticAnalysis {} 5 true).splitOn "Declarations: 0").length > 1)

  let tieManifest : Manifest := {
    sites := #[
      { id := 0, file := "T.lean", decl := "T.a", line := 1, col := 1, kind := .ifThen },
      { id := 1, file := "T.lean", decl := "T.b", line := 5, col := 1, kind := .ifThen },
      { id := 2, file := "T.lean", decl := "T.c", line := 5, col := 9, kind := .ifElse },
      { id := 3, file := "T.lean", decl := "T.c", line := 5, col := 5, kind := .ifThen },
      { id := 4, file := "T.lean", decl := "T.c", line := 3, col := 2, kind := .ifThen },
      { id := 5, file := "SitesOnly.lean", decl := "Ghost", line := 2, col := 1, kind := .ifThen }
    ]
    functions := #[
      { name := "T.a", file := "T.lean", line := 1, endLine := 2, lines := 2, cc := 10, cognitive := 10, siteIds := #[0] },
      { name := "T.b", file := "T.lean", line := 5, endLine := 6, lines := 2, cc := 10, cognitive := 10, siteIds := #[1] },
      { name := "T.cogHi", file := "T.lean", line := 6, endLine := 7, lines := 2, cc := 10, cognitive := 14, siteIds := #[1] },
      { name := "T.cogLo", file := "T.lean", line := 6, endLine := 7, lines := 2, cc := 10, cognitive := 6, siteIds := #[1] },
      { name := "T.ccHi", file := "T.lean", line := 6, endLine := 7, lines := 2, cc := 14, cognitive := 10, siteIds := #[1] },
      { name := "T.ccLo", file := "T.lean", line := 6, endLine := 7, lines := 2, cc := 6, cognitive := 10, siteIds := #[1, 999] },
      { name := "T.z", file := "T.lean", line := 6, endLine := 7, lines := 2, cc := 10, cognitive := 10, siteIds := #[1] },
      { name := "T.c", file := "T.lean", line := 3, endLine := 8, lines := 6, cc := 10, cognitive := 20, siteIds := #[2, 3, 4] },
      { name := "T.mid", file := "T.lean", line := 8, endLine := 9, lines := 2, cc := 14, cognitive := 20, siteIds := #[2, 3] },
      { name := "T.big", file := "T.lean", line := 9, endLine := 12, lines := 4, cc := 20, cognitive := 16, siteIds := #[] },
      { name := "T.low", file := "T.lean", line := 13, endLine := 14, lines := 2, cc := 2, cognitive := 1, siteIds := #[0] },
      { name := "T.empty", file := "OnlyFn.lean", line := 1, endLine := 1, lines := 1, cc := 1, cognitive := 0, siteIds := #[] }
    ]
  }
  let tieRep := buildReport tieManifest #[0, 0, 0, 1, 0, 1]
  check "tieRep crapOver30 >= 3" (tieRep.crapOver30 ≥ 3)
  check "tieRep cogCrapOver30 >= 4" (tieRep.cogCrapOver30 ≥ 4)
  for key in #[SortKey.crap, .cog, .cc, .uncov, .cov] do
    let txt := formatReport tieRep 12 key true true true
    check s!"tie formatReport({key.toString})" ((txt.splitOn "T.a").length > 1)
  let covTieFileTxt := formatReport tieRep 12 .cov true false false
  check "formatReport .cov with multiple files" ((covTieFileTxt.splitOn "OnlyFn.lean").length > 1)
  let emptyHtmlDir := ".lake/build/tmp_empty_html"
  writeHtmlReport ⟨emptyHtmlDir⟩ ⟨"."⟩ {} #[] emptyRep
  check "empty writeHtmlReport wrote index" (← ((⟨emptyHtmlDir⟩ : System.FilePath) / "index.html").pathExists)
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", emptyHtmlDir] }
  check "formatReport showMissed=false" (((formatReport tieRep 5 .crap false false false).splitOn "missed lines:").length == 1)
  check "formatReport topN=0 omits table" (((formatReport tieRep 0 .crap false false false).splitOn "Top ").length == 1)
  check "staticAnalysis >15 counters" (((formatStaticAnalysis tieManifest 10 true).splitOn "(>15:").length > 1)
  check "staticAnalysis cc tie-break" (((formatStaticAnalysis tieManifest 10 false).splitOn "T.big").length > 1)
  check "staticAnalysis topN=0" (((formatStaticAnalysis tieManifest 0 false).splitOn "Top ").length == 1)
  let tieLcov := toLcov tieManifest #[0, 0, 0, 1, 0, 1]
  check "tie lcov includes OnlyFn.lean" ((tieLcov.splitOn "SF:OnlyFn.lean").length > 1)
  check "tie lcov includes SitesOnly.lean (FNF:0)" ((tieLcov.splitOn "SF:SitesOnly.lean").length > 1)

  -- Rich diagnostics: parseGitUnifiedDiff, buildPatchReport, formatMissedDetail, formatHotSites,
  -- formatReportMarkdown, and computeDiffReport / formatDiffReport / formatDiffMarkdown
  let diffSample := "diff --git a/src/Foo.lean b/src/Foo.lean
--- a/src/Foo.lean
+++ b/src/Foo.lean
@@ -9,0 +10,2 @@
+  if x then ...
+  else ...
@@ -15,1 +16,0 @@
-removed line
@@ -20 +25 @@
+single line
@@ bad @@
diff --git a/Plain.lean b/Plain.lean
+++ Plain.lean
@@ -1 +3,1 @@
+plain
diff --git a/src/Dead.lean b/src/Dead.lean
+++ /dev/null
"
  let parsedDiff := parseGitUnifiedDiff diffSample
  checkEq "parsedDiff Foo.lean lines" (parsedDiff.getD "src/Foo.lean" #[]) #[10, 11, 25]
  checkEq "parsedDiff Plain.lean lines" (parsedDiff.getD "Plain.lean" #[]) #[3]
  check "empty git diff" (parseGitUnifiedDiff "").isEmpty
  let patchRep := buildPatchReport manifest hits "origin/main" parsedDiff
  checkEq "patchRep sitesTotal" patchRep.sitesTotal 2
  checkEq "patchRep sitesHit" patchRep.sitesHit 2
  check "formatPatchReport mentions baseRef" (((formatPatchReport patchRep).splitOn "origin/main").length > 1)
  let missedPatchRep := buildPatchReport manifest #[0, 0, 0, 0, 0] "HEAD~1" parsedDiff
  check "formatPatchReport lists missed patch branch" (((formatPatchReport missedPatchRep).splitOn "missed patch branch").length > 1)
  let zeroPatch := buildPatchReport {} #[] "HEAD" ∅
  check "formatPatchReport 0 changed sites" (((formatPatchReport zeroPatch).splitOn "0 changed branch sites").length > 1)

  let hotTxt := formatHotSites manifest hits 3
  check "formatHotSites lists Foo.linear count 10 first" ((hotTxt.splitOn "Foo.linear").length > 1)
  check "formatHotSites 0 hits" (((formatHotSites manifest #[] 5).splitOn "no hits").length > 1)
  let mdTxt := formatReportMarkdown rep 5 .cog (some missedPatchRep)
  check "formatReportMarkdown has header & patch" ((mdTxt.splitOn "## LeanCov Report").length > 1 && (mdTxt.splitOn "Missed Patch Branches").length > 1)
  let mdZeroPatch := formatReportMarkdown rep 0 .cog (some zeroPatch)
  check "formatReportMarkdown 0-site patch" ((mdZeroPatch.splitOn "| Patch branches").length > 1)

  let srcTmp : System.FilePath := ".lake/build/tmp_detail_src"
  IO.FS.createDirAll srcTmp
  let mut demoLines := Array.replicate 25 "  -- filler"
  demoLines := demoLines.set! 19 "  match k with"
  demoLines := demoLines.set! 20 ("  | .other => " ++ String.ofList (List.replicate 110 'x'))
  demoLines := demoLines.set! 21 ""
  IO.FS.writeFile (srcTmp / "Foo.lean") ("\n".intercalate demoLines.toList ++ "\n")
  let detailEmpty ← formatMissedDetail manifest hits #[] srcTmp
  checkEq "formatMissedDetail empty fns" detailEmpty ""
  let detailAllHit ← formatMissedDetail manifest #[1, 1, 1, 1, 1] rep.functions srcTmp
  checkEq "formatMissedDetail all covered" detailAllHit ""
  let multiSiteManifest : Manifest := {
    sites := #[
      { id := 0, file := "Foo.lean", decl := "Foo.baz", line := 22, col := 1, kind := .ifThen },
      { id := 1, file := "Foo.lean", decl := "Foo.baz", line := 21, col := 8, kind := .ifElse },
      { id := 2, file := "Foo.lean", decl := "Foo.baz", line := 21, col := 3, kind := .matchArm },
      { id := 3, file := "Foo.lean", decl := "Foo.baz", line := 999, col := 1, kind := .ifThen }
    ]
    functions := #[rep.functions[1]!.name |> fun n => { name := n, file := "Foo.lean", line := 19, endLine := 22, lines := 4, cc := 10, cognitive := 2, siteIds := #[0, 1, 2, 3] }]
  }
  let detailOk ← formatMissedDetail multiSiteManifest #[0, 0, 0, 0] #[rep.functions[0]!, rep.functions[1]!] srcTmp
  check "formatMissedDetail truncates >96 chars & sorts sites" ((detailOk.splitOn "...").length > 1 && (detailOk.splitOn "Foo.lean:21:3").length > 1)
  let detailMissing ← formatMissedDetail manifest hits rep.functions (srcTmp / "nonexistent")
  check "formatMissedDetail tolerates missing srcRoot" ((detailMissing.splitOn "Foo.lean:21:3").length > 1)
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", srcTmp.toString] }

  -- Diff report: empty, unchanged, regressed (via crapDelta & cogCrapDelta), improved, addedUncovered & addedCovered
  let emptyDiff := computeDiffReport emptyRep emptyRep
  checkEq "empty diff regressed" emptyDiff.regressed.size 0
  let baseRep : SummaryReport := {
    sitesTotal := 10, sitesHit := 8, branchCov := 0.8
    linesTotal := 10, linesHit := 8, lineCov := 0.8
    functionsTotal := 4, functionsHit := 3
    maxCrap := 12.0, maxCogCrap := 10.0, avgCrap := 7.0, avgCogCrap := 6.0
    crapOver30 := 0, cogCrapOver30 := 0, files := #[]
    functions := #[
      { name := "Reg", file := "A.lean", line := 1, endLine := 10, lines := 10, cc := 6, cognitive := 5, sitesTotal := 4, sitesHit := 4, branchCov := 1.0, crap := 6.0, cogCrap := 5.0 },
      { name := "RegCrapOnly", file := "A.lean", line := 3, endLine := 6, lines := 4, cc := 4, cognitive := 1, sitesTotal := 2, sitesHit := 2, branchCov := 1.0, crap := 4.0, cogCrap := 1.0 },
      { name := "Imp", file := "A.lean", line := 12, endLine := 20, lines := 9, cc := 5, cognitive := 5, sitesTotal := 4, sitesHit := 0, branchCov := 0.0, crap := 30.0, cogCrap := 30.0 },
      { name := "ImpCrapOnly", file := "A.lean", line := 22, endLine := 25, lines := 4, cc := 4, cognitive := 1, sitesTotal := 2, sitesHit := 0, branchCov := 0.0, crap := 20.0, cogCrap := 1.0 },
      { name := "Same", file := "A.lean", line := 26, endLine := 28, lines := 3, cc := 2, cognitive := 1, sitesTotal := 1, sitesHit := 1, branchCov := 1.0, crap := 2.0, cogCrap := 1.0 }
    ]
  }
  let headRep : SummaryReport := {
    sitesTotal := 12, sitesHit := 8, branchCov := 0.667
    linesTotal := 12, linesHit := 8, lineCov := 0.667
    functionsTotal := 6, functionsHit := 4
    maxCrap := 42.0, maxCogCrap := 30.0, avgCrap := 18.0, avgCogCrap := 13.0
    crapOver30 := 1, cogCrapOver30 := 0, files := #[]
    functions := #[
      { name := "Reg", file := "A.lean", line := 1, endLine := 10, lines := 10, cc := 6, cognitive := 5, sitesTotal := 4, sitesHit := 0, branchCov := 0.0, crap := 42.0, cogCrap := 30.0 },
      { name := "RegCrapOnly", file := "A.lean", line := 3, endLine := 6, lines := 4, cc := 4, cognitive := 1, sitesTotal := 2, sitesHit := 1, branchCov := 0.5, crap := 6.0, cogCrap := 1.0 },
      { name := "Imp", file := "A.lean", line := 12, endLine := 20, lines := 9, cc := 5, cognitive := 5, sitesTotal := 4, sitesHit := 4, branchCov := 1.0, crap := 5.0, cogCrap := 5.0 },
      { name := "ImpCrapOnly", file := "A.lean", line := 22, endLine := 25, lines := 4, cc := 4, cognitive := 1, sitesTotal := 2, sitesHit := 2, branchCov := 1.0, crap := 4.0, cogCrap := 1.0 },
      { name := "Same", file := "A.lean", line := 26, endLine := 28, lines := 3, cc := 2, cognitive := 1, sitesTotal := 1, sitesHit := 1, branchCov := 1.0, crap := 2.0, cogCrap := 1.0 },
      { name := "NewUncov", file := "B.lean", line := 5, endLine := 12, lines := 8, cc := 4, cognitive := 4, sitesTotal := 2, sitesHit := 0, branchCov := 0.0, crap := 20.0, cogCrap := 20.0 },
      { name := "NewUncov2", file := "B.lean", line := 15, endLine := 18, lines := 4, cc := 3, cognitive := 2, sitesTotal := 2, sitesHit := 0, branchCov := 0.0, crap := 12.0, cogCrap := 6.0 },
      { name := "NewCov", file := "B.lean", line := 20, endLine := 21, lines := 2, cc := 1, cognitive := 0, sitesTotal := 1, sitesHit := 1, branchCov := 1.0, crap := 1.0, cogCrap := 0.0 }
    ]
  }
  let dr := computeDiffReport baseRep headRep
  checkEq "diff regressed count" dr.regressed.size 2
  checkEq "diff improved count" dr.improved.size 2
  checkEq "diff addedUncovered count" dr.addedUncovered.size 2
  check "formatDiffReport shows sections"
    (((formatDiffReport dr 10).splitOn "Regressed functions").length > 1 &&
     ((formatDiffReport dr 10).splitOn "Added uncovered").length > 1 &&
     ((formatDiffReport dr 10).splitOn "Improved functions").length > 1)
  check "formatDiffReport topN=0 omits lists" (((formatDiffReport dr 0).splitOn "Regressed functions").length == 1)
  check "formatDiffMarkdown renders tables" (((formatDiffMarkdown dr 10).splitOn "| Branches |").length > 1)
  check "formatDiffMarkdown topN=0 omits lists" (((formatDiffMarkdown dr 0).splitOn "### Regressed").length == 1)

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
  checkEq "cli analyze multi-src cc" (← LeanCov.CLI.runCLI ["analyze", "--src", (pkgToml / "Lib").toString, "--src", (pkgLean / "Src").toString, "--exclude", "Nope", "--imports", "Init", "--sort", "cc"]) 0
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
  -- Multi-`--src` instrument with a parse-error file to exercise prefixing & skipped warning loop
  let badSrcDir := dir / "bad_src_dir"
  IO.FS.createDirAll badSrcDir
  IO.FS.writeFile (badSrcDir / "BrokenInst.lean") "def oops ( :=\n"
  checkEq "cli instrument multi-src + skipped warning" (← LeanCov.CLI.runCLI [
    "instrument", "--src", (pkgToml / "Lib").toString, "--src", badSrcDir.toString,
    "--out", (dir / "multi_inst").toString, "--sites", (dir / "multi_sites.json").toString
  ]) 0
  checkEq "cli instrument missing src" (← LeanCov.CLI.runCLI ["instrument", "--sites", instSites.toString]) 2
  checkEq "cli instrument missing sites" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString]) 2
  checkEq "cli instrument missing out" (← LeanCov.CLI.runCLI ["instrument", "--src", (pkgToml / "Lib").toString, "--sites", instSites.toString]) 2
  checkEq "cli instrument unknown opt" (← LeanCov.CLI.runCLI ["instrument", "--bogus"]) 2

  -- `stage` error paths
  checkEq "cli stage unknown opt" (← LeanCov.CLI.runCLI ["stage", "--bogus"]) 2
  checkEq "cli stage bad --dep" (← LeanCov.CLI.runCLI ["stage", "--dep", "notapair", "--out", (dir / "err1").toString, "--self"]) 2
  checkEq "cli stage empty --dep val" (← LeanCov.CLI.runCLI ["stage", "--dep", "k=", "--out", (dir / "err1").toString, "--self"]) 2
  checkEq "cli stage empty --dep key" (← LeanCov.CLI.runCLI ["stage", "--dep", "=v", "--out", (dir / "err1").toString, "--self"]) 2
  checkEq "cli stage missing --out" (← LeanCov.CLI.runCLI ["stage", "--pkg", pkgToml.toString, "--self"]) 2
  -- Omitting `--leancov` auto-detects the enclosing `leancov` checkout from `IO.appPath`
  checkEq "cli stage auto-detects --leancov" (← LeanCov.CLI.runCLI ["stage", "--pkg", pkgToml.toString, "--out", (dir / "auto_lc").toString, "--src-dir", "Lib"]) 0
  check "cli stage auto-detect wrote lakefile.toml" (← (dir / "auto_lc" / "lakefile.toml").pathExists)

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
  -- Also exercise instrumentTree on an empty directory + excluded file in analyzeOnly & non-armMains modes
  let emptySrc := dir / "empty_src"
  IO.FS.createDirAll emptySrc
  let mEmpty ← instrumentTree emptySrc (dir / "empty_out") {}
  checkEq "instrumentTree empty dir sites" mEmpty.sites.size 0
  let mNoArm ← instrumentTree (pkgSelf / "Mod") (dir / "no_arm_out") { exclude := #["", "ExcludedMain.lean"] } 0 "Pfx/" (armMains := false)
  check "instrumentTree non-armMains wrote output" (!mNoArm.armOnMain && !mNoArm.sites.isEmpty)
  checkEq "relativeTo non-matching base" (relativeTo ⟨"/other/root"⟩ ⟨"/different/file.lean"⟩) "/different/file.lean"
  checkEq "relativeTo trailing slash base" (relativeTo ⟨"/a/b/"⟩ ⟨"/a/b/c.lean"⟩) "c.lean"
  let mAnalyzeExcl ← instrumentTree (pkgSelf / "Mod") (pkgSelf / "Mod") { exclude := #["ExcludedMain.lean"], analyzeOnly := true }
  check "instrumentTree analyzeOnly skipped parse error" (!mAnalyzeExcl.skippedFiles.isEmpty)
  let selfLeanOut ← IO.FS.readFile (selfStageOut / "lakefile.lean")
  check "stage --self did not duplicate require leancov" ((selfLeanOut.splitOn "require leancov").length == 2)
  check "stage --self preserved https URL" ((selfLeanOut.splitOn "https://example.com/repo").length > 1)
  -- Also cover `--leancov` equal to `--pkg` (implicit isSelf) and lakefile.toml with existing leancov + abs path
  let pkgSelfToml := dir / "pkg_self_toml"
  IO.FS.createDirAll (pkgSelfToml / "Mod")
  IO.FS.createDirAll (pkgSelfToml / "NoMainDir")
  IO.FS.createDirAll (pkgSelfToml / "NestedMain" / ".git")
  IO.FS.createDirAll (pkgSelfToml / "NestedMain" / "Sub")
  IO.FS.createDirAll (pkgSelfToml / ".lake" / "packages")
  IO.FS.writeFile (pkgSelfToml / "lean-toolchain") "\n"
  IO.FS.writeFile (pkgSelfToml / "lakefile.toml")
    "name = \"selftoml\"\n[[require]]\nname = \"leancov\"\npath = \"/abs/lc\"\n"
  IO.FS.writeFile (pkgSelfToml / "lake-manifest.json")
    "{\"version\":\"1.3.0\",\"packages\":[{\"type\":\"path\",\"name\":\"leancov\",\"dir\":\"/abs/lc\"},{\"type\":\"path\",\"name\":\"relpkg\",\"dir\":\"../rel\"},{\"type\":\"git\",\"name\":\"std\"}]}"
  IO.FS.writeFile (pkgSelfToml / "Mod" / "M.lean") "def m (x : Nat) : Nat := x + 1\n"
  IO.FS.writeFile (pkgSelfToml / "NoMainDir" / "Helper.lean") "def helperOnly (x : Nat) : Nat := x\n"
  IO.FS.writeFile (pkgSelfToml / "NestedMain" / "Sub" / "Main.lean") "def main : IO Unit := pure ()\n"
  checkEq "cli stage --leancov + --self + nested main" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgSelfToml.toString, "--out", (dir / "stage_self_toml").toString,
    "--leancov", ".", "--src-dir", "Mod"
  ]) 0
  checkEq "cli stage explicit --leancov --self" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgSelfToml.toString, "--out", (dir / "stage_self_toml2").toString,
    "--leancov", pkgSelfToml.toString, "--self", "--src-dir", "Mod"
  ]) 0

  -- Cross-toolchain `.leancov-pkg` isolation + nested `copyDirArmingMains` subdirectories & binary assets
  let pkgCross := dir / "pkg_cross_tc"
  IO.FS.createDirAll (pkgCross / "Lib")
  IO.FS.createDirAll (pkgCross / "Runner" / "Sub")
  IO.FS.writeFile (pkgCross / "lean-toolchain") "leanprover/lean4:v4.34.1\n"
  IO.FS.writeFile (pkgCross / "lakefile.toml") "[package]\nname = \"crosstc\"\n[[require]]\nname = \"absdep\"\npath = \"/abs/dep\"\n"
  IO.FS.writeFile (pkgCross / "lake-manifest.json") "{\"version\":\"1.3.0\"}"
  IO.FS.writeFile (pkgCross / "Lib" / "Core.lean") "def coreFn (n : Nat) : Nat := if n > 0 then n else 1\n"
  IO.FS.writeFile (pkgCross / "Runner" / "Main.lean") "def main : IO Unit := pure ()\n"
  IO.FS.writeFile (pkgCross / "Runner" / "Sub" / "Helper.lean") "def h (x : Nat) : Nat := x\n"
  IO.FS.writeFile (pkgCross / "Runner" / "Sub" / "data.bin") "raw"
  let stageCross := dir / "stage_cross_tc"
  checkEq "cli stage cross-toolchain isolates .leancov-pkg" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkgCross.toString, "--out", stageCross.toString,
    "--leancov", ".", "--src-dir", "Lib", "--sites", (dir / "fresh_append_sites.json").toString, "--append-sites"
  ]) 0
  check "materialized .leancov-pkg/lakefile.lean" (← (stageCross / ".leancov-pkg" / "lakefile.lean").pathExists)
  check "copied Runner/Sub/data.bin via copyDirArmingMains" (← (stageCross / "Runner" / "Sub" / "data.bin").pathExists)

  -- `run` + `report` (with --files, --kinds, --missed, --json, --lcov, and CI pass/fail gates)
  let prof := dir / "p.cov"
  let freshAppendProf := dir / "fresh_append.cov"
  checkEq "cli run --append on non-existent profile + unarmed sites" (← LeanCov.CLI.runCLI [
    "run", "--sites", instSites.toString, "--profile", freshAppendProf.toString, "--append", "--", "true"
  ]) 0
  checkEq "cli report missing profile-dir + empty profile-dir" (← LeanCov.CLI.runCLI [
    "report", "--sites", instSites.toString, "--profile-dir", (dir / "no_such_prof_dir").toString,
    "--profile-dir", (pkgCross / "Lib").toString
  ]) 2
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
    "--json", repJson.toString, "--lcov", repLcov.toString,
    "--min-cov", "0.0", "--max-crap", "100.0", "--max-cog-crap", "100.0"
  ]) 0
  let badSitesFile := dir / "bad_sites.json"
  IO.FS.writeFile badSitesFile "{invalid json"
  check "cli report invalid sites.json throws" (← catchesIO (LeanCov.CLI.runCLI [
    "report", "--sites", badSitesFile.toString, "--profile", prof.toString
  ]))
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
  checkEq "cli report bad min-patch-cov" (← LeanCov.CLI.runCLI ["report", "--sites", combinedSites.toString, "--profile", prof.toString, "--min-patch-cov", "nope"]) 2

  -- `merge`, rich `report` flags (--missed-detail, --hot, --markdown, --git-diff), and `diff`
  let mergedCov := dir / "merged.cov"
  checkEq "cli merge ok" (← LeanCov.CLI.runCLI ["merge", "--out", mergedCov.toString, "--profile", prof.toString, "--profile-dir", (dir / "pid_prof").toString]) 0
  check "cli merge wrote file" (← mergedCov.pathExists)
  checkEq "cli merge missing out" (← LeanCov.CLI.runCLI ["merge", "--profile", prof.toString]) 2
  checkEq "cli merge missing profile" (← LeanCov.CLI.runCLI ["merge", "--out", mergedCov.toString]) 2
  checkEq "cli merge unknown opt" (← LeanCov.CLI.runCLI ["merge", "--bogus"]) 2

  -- Real temporary git repo to exercise `report --git-diff` + `--min-patch-cov` + `--missed-detail` + `--hot` + `--markdown`
  let gitPkg := dir / "git_patch_repo"
  IO.FS.createDirAll (gitPkg / "Mod")
  IO.FS.writeFile (gitPkg / "Mod" / "Logic.lean") "def f (x : Nat) : Nat := x\n"
  let _ ← IO.Process.output { cmd := "git", args := #["-C", gitPkg.toString, "init"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", gitPkg.toString, "config", "user.email", "ci@example.com"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", gitPkg.toString, "config", "user.name", "CI"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", gitPkg.toString, "add", "."] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", gitPkg.toString, "commit", "-m", "init"] }
  IO.FS.writeFile (gitPkg / "Mod" / "Logic.lean") "def f (x : Nat) : Nat :=\n  if x > 0 then x else 0\n"
  let gitSites := dir / "git_sites.json"
  let gitInstOut := dir / "git_inst_out"
  checkEq "instrument git repo" (← LeanCov.CLI.runCLI ["instrument", "--src", (gitPkg / "Mod").toString, "--out", gitInstOut.toString, "--sites", gitSites.toString]) 0
  let gitManifest ← needE "parse git sites" id (Json.parse (← IO.FS.readFile gitSites) >>= fromJson? : Except String Manifest)
  let gitProf := dir / "git_run.cov"
  let mut gitHits := Array.replicate gitManifest.sites.size (0 : UInt64)
  if gitHits.size > 0 then gitHits := gitHits.set! 0 5
  writeProfile gitProf gitHits
  let repMd := dir / "rep.md"
  let repPatchJson := dir / "rep_patch.json"
  checkEq "cli report --git-diff + --markdown + --hot + --missed-detail (min-patch-cov 40 pass)" (← LeanCov.CLI.runCLI [
    "report", "--sites", gitSites.toString, "--profile", gitProf.toString,
    "--missed-detail", "--src-root", (gitPkg / "Mod").toString, "--hot",
    "--markdown", repMd.toString, "--json", repPatchJson.toString,
    "--git-diff", "HEAD", "--repo", gitPkg.toString, "--min-patch-cov", "40.0"
  ]) 0
  check "report wrote markdown" (← repMd.pathExists)
  checkEq "cli report --min-patch-cov 80 fails" (← LeanCov.CLI.runCLI [
    "report", "--sites", gitSites.toString, "--profile", gitProf.toString,
    "--git-diff", "HEAD", "--repo", gitPkg.toString, "--min-patch-cov", "80.0", "--top", "0"
  ]) 1
  checkEq "cli report bad --git-diff ref exits 2" (← LeanCov.CLI.runCLI [
    "report", "--sites", gitSites.toString, "--profile", gitProf.toString,
    "--git-diff", "nonexistent_ref_xyz", "--repo", gitPkg.toString
  ]) 2

  -- `diff` CLI subcommand (pass, fail on cov-drop, fail on crap-delta, validation errors)
  let baseCov := dir / "git_base.cov"
  writeProfile baseCov (Array.replicate gitManifest.sites.size (2 : UInt64))
  let baseRepJson := dir / "base_rep.json"
  checkEq "generate base_rep.json" (← LeanCov.CLI.runCLI [
    "report", "--sites", gitSites.toString, "--profile", baseCov.toString, "--json", baseRepJson.toString, "--top", "0"
  ]) 0
  let diffJson := dir / "diff.json"
  let diffMd := dir / "diff.md"
  checkEq "cli diff ok" (← LeanCov.CLI.runCLI [
    "diff", "--base", repPatchJson.toString, "--head", baseRepJson.toString,
    "--json", diffJson.toString, "--markdown", diffMd.toString,
    "--max-cov-drop", "5.0", "--max-crap-delta", "5.0", "--top", "10"
  ]) 0
  check "cli diff wrote json & md" ((← diffJson.pathExists) && (← diffMd.pathExists))
  checkEq "cli diff fails on --max-cov-drop" (← LeanCov.CLI.runCLI [
    "diff", "--base", baseRepJson.toString, "--head", repPatchJson.toString, "--max-cov-drop", "5.0"
  ]) 1
  checkEq "cli diff fails on --max-crap-delta" (← LeanCov.CLI.runCLI [
    "diff", "--base", baseRepJson.toString, "--head", repPatchJson.toString, "--max-crap-delta", "0.1"
  ]) 1
  checkEq "cli diff missing base" (← LeanCov.CLI.runCLI ["diff", "--head", baseRepJson.toString]) 2
  checkEq "cli diff missing head" (← LeanCov.CLI.runCLI ["diff", "--base", baseRepJson.toString]) 2
  checkEq "cli diff bad --top" (← LeanCov.CLI.runCLI ["diff", "--base", baseRepJson.toString, "--head", baseRepJson.toString, "--top", "abc"]) 2
  checkEq "cli diff bad --max-cov-drop" (← LeanCov.CLI.runCLI ["diff", "--base", baseRepJson.toString, "--head", baseRepJson.toString, "--max-cov-drop", "abc"]) 2
  checkEq "cli diff bad --max-crap-delta" (← LeanCov.CLI.runCLI ["diff", "--base", baseRepJson.toString, "--head", baseRepJson.toString, "--max-crap-delta", "abc"]) 2
  checkEq "cli diff unknown opt" (← LeanCov.CLI.runCLI ["diff", "--bogus"]) 2

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
  -- `require` pass & fail + `minimizeInput` shrinker
  LeanCov.Fuzz.require true "ok"
  check "Fuzz.require throws on false" (← catchesIO (LeanCov.Fuzz.require false "boom"))
  let shrinkTarget : LeanCov.Fuzz.Target := {
    name := "shrink"
    seeds := #[⟨#[0x7A]⟩]
    check := fun _ bs => do
      for i in [:bs.size] do
        if bs[i]! == 0x7A then throw (IO.userError "hit 0x7A")
      return true
  }
  let shrunk ← LeanCov.Fuzz.minimizeInput shrinkTarget ⟨#[1, 2, 0x7A, 4, 5]⟩
  check "minimizeInput shrinks to 1 byte" (shrunk == ⟨#[0x7A]⟩)

  -- End-to-end `Fuzz.main` supervisor + child + corpus replay + finding + bad option
  let fuzzBin := ((← IO.appPath).parent.getD ".lake/build/bin") / "leancov-fuzz-test"
  if ← fuzzBin.pathExists then
    let fdir : System.FilePath := ".lake/build/tmp_fuzz_e2e"
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", fdir.toString] }
    IO.FS.createDirAll (fdir / "corpus" / "clean")
    IO.FS.writeBinFile (fdir / "corpus" / "clean" / "seed1.bin") "abc".toUTF8
    IO.FS.writeFile (fdir / "corpus" / "clean" / "README.txt") "ignored"
    -- 1. Clean run with corpus replay (and ignored non-.bin file) + uppercase hex seed & --target all
    let okOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "all", "--iterations", "20", "--seed", "0x4A", "--max-input", "64"]
      env := #[("LEANCOV_TEST_CORPUS", some (fdir / "corpus").toString)]
    }
    check "fuzz all + hex seed fails on intentional finding target" (okOut.exitCode == 1)
    let okClean ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "clean", "--iterations", "50", "--seed", "0x4f", "--max-input", "64"]
      env := #[("LEANCOV_TEST_CORPUS", some (fdir / "corpus").toString)]
    }
    check "fuzz clean + corpus passes" (okClean.exitCode == 0) s!"{okClean.stdout}{okClean.stderr}"
    -- 2. Finding caught, minimized, & saved (with decimal seed), plus `--no-minimize`
    let findOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "finding", "--iterations", "50", "--seed", "66", "--save", (fdir / "saved").toString]
    }
    checkEq "fuzz finding exits 1" findOut.exitCode 1
    check "fuzz finding saved .bin" (← (fdir / "saved" / "finding-0x42.bin").pathExists)
    let findNoMin ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "finding", "--iterations", "50", "--seed", "66", "--no-minimize"]
    }
    checkEq "fuzz finding --no-minimize exits 1" findNoMin.exitCode 1
    -- Coverage-guided corpus growth & `--no-guided`
    let guidedOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "guided", "--iterations", "40", "--seed", "0x55", "--max-input", "32"]
    }
    checkEq "fuzz guided exits 0" guidedOut.exitCode 0
    check "fuzz guided grew corpus" ((guidedOut.stdout.splitOn "corpus +").length > 1)
    let noGuidedOut ← IO.Process.output {
      cmd := fuzzBin.toString
      args := #["--target", "guided", "--iterations", "20", "--no-guided"]
    }
    checkEq "fuzz --no-guided exits 0" noGuidedOut.exitCode 0
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
    -- 5. Unknown target exits 2 + corpus error paths + 0-iteration clean run
    let unkOut ← IO.Process.output { cmd := fuzzBin.toString, args := #["--target", "doesnotexist", "--iterations", "1"] }
    checkEq "fuzz unknown target exits 2" unkOut.exitCode 2
    let zeroIter ← IO.Process.output { cmd := fuzzBin.toString, args := #["--target", "clean", "--iterations", "0"] }
    checkEq "fuzz 0 iterations exits 0" zeroIter.exitCode 0
    let missingCorp ← IO.Process.output {
      cmd := fuzzBin.toString, args := #["--target", "clean", "--iterations", "1"]
      env := #[("LEANCOV_TEST_CORPUS", some (fdir / "no_such_corpus").toString)]
    }
    check "fuzz missing corpus dir fails" (missingCorp.exitCode != 0)
    IO.FS.createDirAll (fdir / "bad_corpus" / "ghost_target")
    let badCorp ← IO.Process.output {
      cmd := fuzzBin.toString, args := #["--target", "clean", "--iterations", "1"]
      env := #[("LEANCOV_TEST_CORPUS", some (fdir / "bad_corpus").toString)]
    }
    check "fuzz unknown corpus subdir fails" (badCorp.exitCode != 0)
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

private unsafe def testMutateEngineAndCLI : TM Unit := do
  -- 1. MutantKind & MutantOutcome JSON round-trips
  for k in #[MutantKind.cmpFlip, .arithFlip, .boolOpFlip, .boolLitFlip, .negRemove, .condNegate] do
    checkEq s!"MutantKind ofString {k.toString}" (MutantKind.ofString? k.toString) (some k)
    let back : Except String MutantKind := fromJson? (toJson k)
    checkEq s!"MutantKind json {k.toString}" back.toOption (some k)
  checkEq "MutantKind unknown" (MutantKind.ofString? "nope") none
  check "MutantKind bad json" (fromJson? (Json.str "nope") : Except String MutantKind).toOption.isNone

  for o in #[MutantOutcome.killed, .proved, .survived, .timeout, .uncompilable, .uncovered] do
    checkEq s!"MutantOutcome ofString {o.toString}" (MutantOutcome.ofString? o.toString) (some o)
    let back : Except String MutantOutcome := fromJson? (toJson o)
    checkEq s!"MutantOutcome json {o.toString}" back.toOption (some o)
  checkEq "MutantOutcome unknown" (MutantOutcome.ofString? "nope") none
  check "MutantOutcome bad json" (fromJson? (Json.str "nope") : Except String MutantOutcome).toOption.isNone

  -- 2. AST-guided mutant discovery & splicing across operators, patterns, proofs, and filters
  let env ← loadParserEnv
  let mutSrc := "
namespace MutDemo
meta def badMutQuot : Unit := `(UnknownCat| x)
structure FlagBox where
  val : Bool

instance : BEq FlagBox where
  beq a b := a.val == b.val

abbrev flipAbb (b : Bool) : Bool := !b

def eqnsMut : Bool → Bool
  | .true => false
  | .false => true

section S
open Nat in
def checkOps (a b : Nat) (x y : Bool) (o : Option Bool) : IO Bool := do
  have _h : a = a := by rfl
  let localInit := false
  let mut bindInit : Bool ← pure true
  let box : FlagBox := { val := (true : Bool) }
  let (p, _) := (box.val, localInit)
  let some q ← pure o | return false
  let some r := o | return Bool.true
  for z in [Bool.false] do
    if let some _ := o then pure ()
  let _propEq := if a = b then 1 else if a ≠ b then 2 else 0
  let _depVal := if _h2 : a < b then true else false
  let _ifLetVal := if let some v := o then v else false
  let _unparenNeg := !Bool.not x
  let _longNeg := !((a < b) && (a <= b) && (a > b) && (a >= b) && bindInit)
  if _hd : a < b then
    let (u, _) ← pure (true, false)
    if !u then return false
  if (x &&
      y) then
    unless y do return !x
  else if (a < b && a <= b && a ≤ b && a > b && a >= b && a ≥ b && a == b && a != b) then
    return !(x || y)
  else
    pure ()
  return if p && q && r && !(id x) then true else false
where
  helper (n : Nat) : Bool := n < 10
end S

theorem skipTheorem (n : Nat) : n = n := rfl
noncomputable def skipNc (b : Bool) : Bool := !b
def skipPropFn (a b : Nat) : Prop := a < b
def skipTacMut : Bool := by exact true

mutual
def m1 (b : Bool) : Bool := if b then m2 false else true
def m2 (b : Bool) : Bool := !b
end
end MutDemo
"
  let allMs ← discoverMutantsInSource env "MutDemo.lean" mutSrc 0 #[]
  check "discovered >= 20 mutants" (allMs.size ≥ 20)
  check "skipped theorem" (!allMs.any (·.decl == "MutDemo.skipTheorem"))
  check "skipped noncomputable" (!allMs.any (·.decl == "MutDemo.skipNc"))
  check "skipped Prop fn" (!allMs.any (·.decl == "MutDemo.skipPropFn"))
  check "has cmpFlip" (allMs.any (·.kind == .cmpFlip))
  check "has boolOpFlip" (allMs.any (·.kind == .boolOpFlip))
  check "has boolLitFlip" (allMs.any (·.kind == .boolLitFlip))
  check "has negRemove" (allMs.any (·.kind == .negRemove))
  check "has condNegate" (allMs.any (·.kind == .condNegate))
  -- Arithmetic/bitwise operators + `-- leancov:ignore-mutant` + `--no-arith`
  let arithSrc := "
def arithOps (a b : Nat) : Nat :=
  let s := (a + b) - (a * 2) / 3
  let bw := (a &&& b) ||| (a <<< 1) >>> 1
  let ign := a + b -- leancov:ignore-mutant
  s + bw + ign
"
  let arithMs ← discoverMutantsInSource env "Arith.lean" arithSrc 0 #[] true
  check "arithOps discovered >= 9 arith mutants" (arithMs.countP (·.kind == .arithFlip) ≥ 9)
  check "leancov:ignore-mutant suppressed line 5" (!arithMs.any (·.line == 5))
  let noArithMs ← discoverMutantsInSource env "Arith.lean" arithSrc 0 #[] false
  checkEq "includeArith=false skips all arithFlip" (noArithMs.countP (·.kind == .arithFlip)) 0
  checkEq "sampleMutants deterministic seed" (sampleMutants arithMs 4 (some 0x1234)) (sampleMutants arithMs 4 (some 0x1234))
  checkEq "sampleMutants empty array" (sampleMutants #[] 4 (some 0x1234)).size 0
  checkEq "sampleMutants unseeded" (sampleMutants arithMs 2 none).size 2
  let diffMs := filterMutantsByGitDiff arithMs ((∅ : Std.HashMap String (Array Nat)).insert "Arith.lean" #[3])
  check "filterMutantsByGitDiff keeps only line 3" (diffMs.all (·.line == 3) && diffMs.size > 0)
  -- `pruneUncoveredMutants`: empty, line-hit kept, line-missed pruned, fn-level fallback hit/missed/empty, unknown decl kept
  let (emptyPruneKeep, emptyPruneDrop) := pruneUncoveredMutants #[] {} #[]
  check "prune empty" (emptyPruneKeep.isEmpty && emptyPruneDrop.isEmpty)
  let pruneManifest : Manifest := {
    sites := #[
      { id := 0, file := "P.lean", decl := "P.hitLine", line := 10, col := 1, kind := .ifThen },
      { id := 1, file := "P.lean", decl := "P.fnCov", line := 30, col := 1, kind := .ifThen },
      { id := 2, file := "P.lean", decl := "P.fnUncov", line := 40, col := 1, kind := .ifThen }
    ]
    functions := #[
      { name := "P.fnCov", file := "P.lean", line := 25, endLine := 32, lines := 8, cc := 2, cognitive := 1, siteIds := #[1] },
      { name := "P.fnUncov", file := "P.lean", line := 35, endLine := 42, lines := 8, cc := 2, cognitive := 1, siteIds := #[2] },
      { name := "P.fnNoSites", file := "P.lean", line := 45, endLine := 46, lines := 2, cc := 1, cognitive := 0, siteIds := #[] }
    ]
  }
  let mkPruneMut (id line : Nat) (decl : String) : Mutant :=
    { id, file := "P.lean", decl, line, col := 1, kind := .boolLitFlip, original := "true", replacement := "false", startByte := 0, endByte := 4, repText := "false" }
  let (keptP, prunedP) := pruneUncoveredMutants #[
    mkPruneMut 0 10 "P.hitLine",
    mkPruneMut 1 26 "P.fnCov",
    mkPruneMut 2 36 "P.fnUncov",
    mkPruneMut 3 45 "P.fnNoSites",
    mkPruneMut 4 50 "P.unknown"
  ] pruneManifest #[3, 2, 0]
  checkEq "prune kept 4 (hitLine, fnCov, fnNoSites, unknown)" keptP.size 4
  checkEq "prune dropped 1 (fnUncov)" prunedP.size 1
  -- Every single spliced mutant must still parse cleanly as valid Lean 4 syntax!
  for m in allMs do
    let mutated := applyMutant mutSrc m
    check s!"mutant #{m.id} changes source" (mutated != mutSrc)
    let r ← instrumentSource env "MutatedCheck.lean" mutated 0 { analyzeOnly := true }
    checkEq s!"mutant #{m.id} ({m.original} -> {m.replacement}) parses cleanly" r.skippedReason none

  let ignMsDefault ← discoverMutantsInSource env "Interp.lean" "def msg (a b : Nat) (ok : Bool) : String := s!\"sum={a + b} ok={!ok}\"\n" 0 #[] true false
  checkEq "interpolatedStr mutations skipped by default" ignMsDefault.size 0
  let ignMsInc ← discoverMutantsInSource env "Interp.lean" "def msg (a b : Nat) (ok : Bool) : String := s!\"sum={a + b} ok={!ok}\"\n" 0 #[] true true
  check "interpolatedStr mutations included when includeInterp=true" (ignMsInc.size ≥ 2)

  let filtMs ← discoverMutantsInSource env "MutDemo.lean" mutSrc 0 #["", "m2"]
  checkEq "filtered to m2 only" filtMs.size 1
  checkEq "m2 mutant decl" filtMs[0]!.decl "MutDemo.m2"
  checkEq "empty source yields 0 mutants" (← discoverMutantsInSource env "Empty.lean" "").size 0
  checkEq "parse error yields 0 mutants" (← discoverMutantsInSource env "Bad.lean" "namespace Broken\ndef broken ( :=\nend Broken\n").size 0
  checkEq "header error yields 0 mutants" (← discoverMutantsInSource env "BadH.lean" "import 123\n").size 0

  -- 3. End-to-end `leancov mutate` on a mini Lake package covering:
  --    killed, survived, uncompilable (dependent array bounds), timeout, --json, --min-score, --keep-work
  let dir : System.FilePath := ".lake/build/tmp_mutate_e2e"
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }
  let pkg := dir / "pkg"
  IO.FS.createDirAll (pkg / "Mini")
  IO.FS.writeFile (pkg / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
  IO.FS.writeFile (pkg / "lakefile.toml")
    "name = \"mini\"\ndefaultTargets = [\"mini-test\"]\n[[lean_lib]]\nname = \"Mini\"\n[[lean_lib]]\nname = \"MiniProofs\"\n[[lean_exe]]\nname = \"mini-test\"\nroot = \"Main\"\n"
  IO.FS.writeFile (pkg / "Mini.lean") "import Mini.Lib\nimport Mini.Spin\n"
  IO.FS.writeFile (pkg / "MiniProofs.lean") "import Mini.Lib\ntheorem Mini.doubleVal_two : Mini.doubleVal 2 = 4 := by decide\n"
  IO.FS.writeFile (pkg / "Mini" / "Lib.lean") "namespace Mini

-- Dependent `h : 0 < xs.size`: mutating `<` -> `≤` fails compilation (`uncompilable`)!
def safeFirst (xs : Array Nat) : Nat :=
  if h : 0 < xs.size then xs[0] else 0

-- Boundary `age >= 18` tested only at 20 and 10 -> `>=` -> `>` SURVIVES!
def isAdult (age : Nat) : Bool :=
  age >= 18

-- Strictly tested at both true and false -> `&&` -> `||` and `true` -> `false` are KILLED!
def strictGate (ok : Bool) : Bool :=
  ok && true

-- Arithmetic proved by theorem in MiniProofs (`+` -> `-` fails `MiniProofs` -> PROVED!)
def doubleVal (x : Nat) : Nat :=
  x + x

-- Never called by `mini-test` -> pruned as UNCOVERED when `--sites`/`--profile` is supplied!
def deadBranch (n : Nat) : Bool :=
  if n > 100 then true else false

end Mini
"
  IO.FS.writeFile (pkg / "Mini" / "Spin.lean") "namespace Mini
def keepGoing : Bool := true
end Mini
"
  IO.FS.writeFile (pkg / "Main.lean") "import Mini
open Mini

def main : IO UInt32 := do
  if safeFirst #[9] != 9 || safeFirst #[] != 0 then return 1
  if !isAdult 20 || isAdult 10 then return 1
  if !strictGate true || strictGate false then return 1
  if doubleVal 2 != 4 then return 1
  return 0
"
  let jsonPath := dir / "mutate.json"
  let mdPath := dir / "mutate.md"
  let workDir := dir / "work"
  -- Run with --min-score 95.0 -> must exit 1 because `isAdult` boundary mutant (`>=` -> `>`) survives!
  let codeFail ← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--out", workDir.toString,
    "--file", "Mini/Lib.lean", "--build-target", "mini-test",
    "--json", jsonPath.toString, "--markdown", mdPath.toString, "--min-score", "95.0",
    "--", ".lake/build/bin/mini-test"
  ]
  checkEq "mutate exits 1 when below --min-score 95" codeFail 1
  check "workDir cleaned up without --keep-work" (!(← workDir.pathExists))
  check "mutate wrote json" (← jsonPath.pathExists)
  check "mutate wrote markdown" (← mdPath.pathExists)
  let mdMutTxt ← IO.FS.readFile mdPath
  check "mutate markdown lists Survived Mutants" ((mdMutTxt.splitOn "### Survived Mutants").length > 1)
  let passMd := formatMutateMarkdown (summarizeMutateResults 1 #[{ mutant := { id := 0, file := "A.lean", decl := "f", line := 1, col := 1, kind := .boolLitFlip, original := "true", replacement := "false", startByte := 0, endByte := 4, repText := "false" }, outcome := .killed, elapsedMs := 1 }])
  check "formatMutateMarkdown 0 survivors omits table" ((passMd.splitOn "### Survived Mutants").length == 1)
  let jRaw ← IO.FS.readFile jsonPath
  let jObj ← needE "parse mutate.json" id (Json.parse jRaw)
  let uncomp ← needE "uncompilable field" id (jObj.getObjValAs? Nat "uncompilable")
  let killed ← needE "killed field" id (jObj.getObjValAs? Nat "killed")
  let survived ← needE "survived field" id (jObj.getObjValAs? Nat "survived")
  let tested ← needE "tested field" id (jObj.getObjValAs? Nat "tested")
  check "at least 1 uncompilable mutant (safeFirst)" (uncomp ≥ 1)
  check "at least 2 killed mutants (strictGate)" (killed ≥ 2)
  check "at least 1 survived mutant (isAdult >= 18)" (survived ≥ 1)
  checkEq "tested == killed + survived" tested (killed + survived)

  -- Re-run filtered to `strictGate` with `--min-score 100`, `--max-mutants 2`, and `--keep-work` -> exits 0!
  let workKept := dir / "work_kept"
  let codePass ← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--out", workKept.toString,
    "--src-dir", "Mini", "--filter", "strictGate", "--max-mutants", "2",
    "--build-target", "mini-test", "--min-score", "100.0", "--keep-work",
    "--", ".lake/build/bin/mini-test"
  ]
  checkEq "mutate strictGate 100% passes" codePass 0
  check "workDir preserved with --keep-work" (← workKept.pathExists)

  -- Fast wall-clock timeout verification (`--no-build --timeout 0.15`)
  let timeoutJson := dir / "timeout.json"
  let codeTimeout ← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--file", "Mini/Spin.lean",
    "--no-build", "--timeout", "0.15", "--json", timeoutJson.toString, "--min-score", "100.0",
    "--", "sh", "-c", "grep -q 'true' Mini/Spin.lean || sleep 5"
  ]
  checkEq "timeout counts toward killed+timeout score 100%" codeTimeout 0
  let tj ← needE "parse timeout.json" id (Json.parse (← IO.FS.readFile timeoutJson))
  let toutCount ← needE "timeout field" id (tj.getObjValAs? Nat "timeout")
  checkEq "recorded 1 timeout mutant" toutCount 1

  -- CLI validation & edge paths (0-mutant 100%, warm cache, lakefile.lean, unmutated binary guard, baseline fail)
  let pkgLeanMut := dir / "pkg_lean_mut"
  IO.FS.createDirAll (pkgLeanMut / "Sub" / "Nested")
  IO.FS.createDirAll (pkgLeanMut / ".git")
  IO.FS.createDirAll (pkgLeanMut / "build")
  IO.FS.createDirAll (pkgLeanMut / "Sub" / ".git")
  IO.FS.createDirAll (pkgLeanMut / ".lake" / "build" / "ir")
  IO.FS.createDirAll (pkgLeanMut / ".lake" / "build" / "bin")
  IO.FS.writeFile (pkgLeanMut / ".lake" / "build" / "ir" / "dummy.c") ""
  IO.FS.writeFile (pkgLeanMut / ".lake" / "build" / "bin" / "unmutated-bin") ""
  IO.FS.writeFile (pkgLeanMut / "lakefile.lean") "import Lake\nopen Lake DSL\npackage p\nrequire g from git \"https://example.com/g\"\nrequire a from \"/abs/a\"\n"
  IO.FS.writeFile (pkgLeanMut / "lake-manifest.json") "[]"
  IO.FS.writeFile (pkgLeanMut / "TopNote.txt") "asset"
  IO.FS.writeFile (pkgLeanMut / "Sub" / "Nested" / "Data.txt") "nested"
  IO.FS.writeFile (pkgLeanMut / "Sub" / "NoMut.lean") "def idNat (n : Nat) : Nat := n\n"
  let okScript := dir / "pass.sh"
  IO.FS.writeFile okScript "#!/bin/sh\nexit 0\n"
  let _ ← IO.Process.output { cmd := "chmod", args := #["+x", okScript.toString] }
  -- 0-mutant run (with comma filter + empty item, --imports, nested --out inside pkg, duplicate --file/--src-dir, callerCwd script) -> 100.0%
  checkEq "mutate 0-mutant 100%" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--out", (pkgLeanMut / "Sub" / "work_in_pkg").toString,
    "--file", (pkgLeanMut / "Sub" / "NoMut.lean").toString, "--file", "Sub/NoMut.lean",
    "--src-dir", "Sub", "--filter", ",idNat,other,", "--imports", "Init", "--no-build", okScript.toString
  ]) 0
  -- Reject --file pointing outside --pkg
  checkEq "mutate rejects file outside pkg" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", (pkg / "Mini" / "Lib.lean").toString, "--", "true"
  ]) 2
  -- Sampled report header (`discovered > generated`) via --max-mutants 1 on Mini/Lib.lean
  checkEq "mutate sampled --max-mutants 1" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--file", "Mini/Lib.lean", "--max-mutants", "1", "--no-build", "--", "true"
  ]) 0
  -- Guard against pointing <testCmd> at unmutated --pkg/.lake/build/bin/* (both abs and rel)
  let absUnmut ← IO.FS.realPath (pkgLeanMut / ".lake" / "build" / "bin" / "unmutated-bin")
  checkEq "mutate rejects abs unmutated pkg/.lake binary" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", "Sub/NoMut.lean", "--no-build",
    "--", absUnmut.toString
  ]) 2
  checkEq "mutate rejects unmutated pkg/.lake binary" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", "Sub/NoMut.lean", "--no-build",
    "--", (pkgLeanMut / ".lake" / "build" / "bin" / "unmutated-bin").toString
  ]) 2
  checkEq "empty instrument args" (← LeanCov.CLI.runCLI ["instrument"]) 2
  checkEq "empty run args" (← LeanCov.CLI.runCLI ["run"]) 2
  checkEq "empty report args" (← LeanCov.CLI.runCLI ["report"]) 2
  checkEq "empty mutate args" (← LeanCov.CLI.runCLI ["mutate"]) 2
  -- Baseline test failure & baseline test timeout exit 2
  checkEq "mutate baseline test failure exits 2" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", "Sub/NoMut.lean", "--no-build", "--", "false"
  ]) 2
  checkEq "mutate baseline test timeout exits 2" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", "Sub/NoMut.lean", "--no-build", "--timeout", "0.1", "--", "sleep", "5"
  ]) 2
  -- Baseline build failure exits 2
  checkEq "mutate baseline build failure exits 2" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--file", "Sub/NoMut.lean",
    "--build-target", "nonexistent-target-xyz", "--", "true"
  ]) 2
  let emptyMutDir := pkgLeanMut / "EmptyDir"
  IO.FS.createDirAll emptyMutDir
  checkEq "mutate empty src-dir exits 2" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkgLeanMut.toString, "--src-dir", "EmptyDir", "--", "true"
  ]) 2
  checkEq "mutate missing cmd" (← LeanCov.CLI.runCLI ["mutate", "--pkg", pkg.toString, "--file", "Mini/Lib.lean"]) 2
  checkEq "mutate missing file/src-dir" (← LeanCov.CLI.runCLI ["mutate", "--pkg", pkg.toString, "--", "true"]) 2
  checkEq "mutate missing file path" (← LeanCov.CLI.runCLI ["mutate", "--pkg", pkg.toString, "--file", "Nope.lean", "--", "true"]) 2
  checkEq "mutate missing src-dir" (← LeanCov.CLI.runCLI ["mutate", "--pkg", pkg.toString, "--src-dir", "NopeDir", "--", "true"]) 2
  checkEq "mutate bad max-mutants" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--max-mutants", "abc", "--", "true"]) 2
  checkEq "mutate zero timeout" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--timeout", "0", "--", "true"]) 2
  checkEq "mutate bad timeout" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--timeout", "abc", "--", "true"]) 2
  checkEq "mutate bad min-score" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--min-score", "abc", "--", "true"]) 2
  -- Coverage-pruned + proof-aware + git-diff + seed mutation campaign on Mini
  let covStage := dir / "cov_stage"
  let covProf := dir / "cov.prof"
  checkEq "stage mini for mutate pruning" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkg.toString, "--out", covStage.toString, "--src-dir", "Mini", "--exclude", "Main.lean"
  ]) 0
  let cb ← IO.Process.output { cmd := "lake", args := #["build", "mini-test"], cwd := some covStage }
  check "mini-test instrumented built" (cb.exitCode == 0)
  checkEq "run mini-test for pruning profile" (← LeanCov.CLI.runCLI [
    "run", "--sites", (covStage / "sites.json").toString, "--profile", covProf.toString, "--",
    (covStage / ".lake" / "build" / "bin" / "mini-test").toString
  ]) 0
  let proofJson := dir / "proof_mutate.json"
  checkEq "mutate with --proof-target + --sites/--profile + --seed" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--out", (dir / "work_proof").toString,
    "--file", "Mini/Lib.lean", "--filter", "doubleVal,deadBranch", "--seed", "0x77",
    "--build-target", "mini-test", "--proof-target", "MiniProofs",
    "--sites", (covStage / "sites.json").toString, "--profile", covProf.toString,
    "--json", proofJson.toString, "--min-score", "100.0",
    "--", ".lake/build/bin/mini-test"
  ]) 0
  let pj ← needE "parse proof_mutate.json" id (Json.parse (← IO.FS.readFile proofJson))
  check "recorded >= 1 proved mutant (doubleVal)" ((pj.getObjValAs? Nat "proved").toOption.getD 0 ≥ 1)
  check "recorded >= 1 uncovered mutant (deadBranch)" ((pj.getObjValAs? Nat "uncovered").toOption.getD 0 ≥ 1)

  -- Git-diff mutation filtering (`--git-diff HEAD`) & `--no-arith` & invalid flag paths
  let _ ← IO.Process.output { cmd := "git", args := #["-C", pkg.toString, "init"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", pkg.toString, "config", "user.email", "ci@example.com"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", pkg.toString, "config", "user.name", "CI"] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", pkg.toString, "add", "."] }
  let _ ← IO.Process.output { cmd := "git", args := #["-C", pkg.toString, "commit", "-m", "base"] }
  IO.FS.writeFile (pkg / "Mini" / "Spin.lean") "namespace Mini\ndef keepGoing : Bool := false\nend Mini\n"
  checkEq "mutate --git-diff --no-arith --include-interp on Spin.lean" (← LeanCov.CLI.runCLI [
    "mutate", "--pkg", pkg.toString, "--file", "Mini/Spin.lean", "--git-diff", "HEAD", "--no-arith", "--include-interp", "--no-build", "--", "true"
  ]) 0
  checkEq "mutate bad --seed" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--seed", "nope", "--", "true"]) 2
  checkEq "mutate --sites without --profile" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--sites", (covStage / "sites.json").toString, "--", "true"]) 2
  checkEq "mutate --profile without --sites" (← LeanCov.CLI.runCLI ["mutate", "--file", "Mini/Lib.lean", "--profile", covProf.toString, "--", "true"]) 2

  checkEq "mutate unknown opt" (← LeanCov.CLI.runCLI ["mutate", "--bogus"]) 2

  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

private unsafe def testV030CLI : TM Unit := do
  let dir : System.FilePath := ".lake/build/tmp_v030_cli"
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }
  let pkg := dir / "pkg"
  IO.FS.createDirAll (pkg / "Mod")
  IO.FS.writeFile (pkg / "lakefile.toml") "name = \"v030\"\n[[lean_lib]]\nname = \"Mod\"\n"
  IO.FS.writeFile (pkg / "Mod" / "Logic.lean")
    "def f (x : Nat) : Nat := if x > 0 then x else 0\n\ndef full (x : Nat) : Nat := if x > 0 then x else 0\n\ndef tbl : Nat := Id.run do\n  let mut s := 0\n  for i in [:4] do\n    s := s + i\n  return s"
  IO.FS.writeFile (pkg / "Mod" / "Empty.lean") "def lin (x : Nat) : Nat := x + 1\n"
  let sitesPath := dir / "sites.json"
  let profPath := dir / "prof.cov"
  checkEq "stage default excludes CAF" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkg.toString, "--out", (dir / "stage_default").toString, "--leancov", ".", "--src-dir", "Mod"
  ]) 0
  checkEq "stage --include-cafs" (← LeanCov.CLI.runCLI [
    "stage", "--pkg", pkg.toString, "--out", (dir / "stage_cafs").toString, "--leancov", ".", "--src-dir", "Mod", "--include-cafs"
  ]) 0
  checkEq "instrument --include-cafs" (← LeanCov.CLI.runCLI [
    "instrument", "--src", (pkg / "Mod").toString, "--out", (dir / "inst_cafs").toString, "--sites", sitesPath.toString, "--include-cafs"
  ]) 0
  let m ← needE "parse v030 sites" id (Json.parse (← IO.FS.readFile sitesPath) >>= fromJson? : Except String Manifest)
  check "instrument --include-cafs includes tbl" (m.functions.any (·.name == "tbl"))
  let mut hits := Array.replicate m.sites.size (0 : UInt64)
  -- Hit site 0 (part of line 1: f if.then hit, if.else missed -> ln-part + warn 50%) and full (100% -> ln-hit + ok)
  if hits.size ≥ 5 then
    hits := (hits.set! 0 3).set! 2 2 |>.set! 3 2 |>.set! 4 1
  writeProfile profPath hits
  let htmlDir := dir / "html_ok"
  checkEq "report --html + --sort cov + --files" (← LeanCov.CLI.runCLI [
    "report", "--sites", sitesPath.toString, "--profile", profPath.toString,
    "--files", "--sort", "cov", "--html", htmlDir.toString, "--src-root", (pkg / "Mod").toString
  ]) 0
  check "html wrote index.html" (← (htmlDir / "index.html").pathExists)
  let logicHtml := htmlDir / "files" / (safeHtmlFileName "Logic.lean")
  check "html wrote source page" (← logicHtml.pathExists)
  let logicTxt ← IO.FS.readFile logicHtml
  check "html source has line anchor, part/hit/miss & badge" (
    (logicTxt.splitOn "id=\"L1\"").length > 1 &&
    (logicTxt.splitOn "ln-part").length > 1 &&
    (logicTxt.splitOn "ln-hit").length > 1 &&
    (logicTxt.splitOn "badge").length > 1
  )
  let htmlMiss := dir / "html_miss"
  checkEq "report --file + --decl + --exclude-kind + missing src" (← LeanCov.CLI.runCLI [
    "report", "--sites", sitesPath.toString, "--profile", profPath.toString,
    "--file", "Logic.lean", "--decl", "f", "--exclude-kind", "if.else",
    "--html", htmlMiss.toString, "--src-root", (dir / "missing_root").toString
  ]) 0
  let missTxt ← IO.FS.readFile (htmlMiss / "files" / (safeHtmlFileName "Logic.lean"))
  check "html missing src renders notice" ((missTxt.splitOn "Source file not found").length > 1)
  checkEq "report invalid --exclude-kind exits 2" (← LeanCov.CLI.runCLI [
    "report", "--sites", sitesPath.toString, "--profile", profPath.toString, "--exclude-kind", "bogus"
  ]) 2
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

unsafe def main : IO UInt32 :=
  runMain "leancov-test" do
    runTest "types & binary profiles" testTypesAndProfiles
    runTest "complexity (CC vs Cognitive)" testComplexity
    runTest "AST instrumentation, runtime semantics & armMain" testInstrumentAndRuntimeSemantics
    runTest "report, kinds & LCOV" testReportAndLcov
    runTest "CLI subcommands end-to-end" testCLISubcommands
    runTest "v0.3.0 filtering, HTML & CAF CLI" testV030CLI
    runTest "fuzz primitives & mutator" testFuzzPrimitives
    runTest "exact binary runtime counters (ground truth)" testExactRuntimeCounters
    runTest "AST mutation engine & mutate CLI" testMutateEngineAndCLI
