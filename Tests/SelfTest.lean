import LeanCov.Check
import LeanCov.Cov

/-! # Full test suite for LeanCov complexity, AST instrumentation, profiles, and reporting -/

open LeanCov.Check LeanCov.Cov

private unsafe def testComplexity : TM Unit := do
  let env ← loadParserEnv
  -- 1. Flat 8-arm match should have high CC (8) but low Cognitive Complexity (1)!
  let flatCode := "
def dispatch (k : Nat) : Nat :=
  match k with
  | 0 => 10
  | 1 => 11
  | 2 => 12
  | 3 => 13
  | 4 => 14
  | 5 => 15
  | 6 => 16
  | _ => 99
"
  let r1 ← instrumentSource env "Flat.lean" flatCode 0 { analyzeOnly := true }
  checkEq "flat function count" r1.functions.size 1
  let f1 := r1.functions[0]!
  checkEq "flat match CC" f1.cc 8
  checkEq "flat match cognitive" f1.cognitive 1
  checkEq "flat match probe sites" f1.siteIds.size 8

  -- 2. Deeply nested control flow should have much higher Cognitive Complexity than CC!
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
  checkEq "nested function count" r2.functions.size 1
  let f2 := r2.functions[0]!
  -- CC = 1 + for(1) + if(1) + if(1) + unless(1) = 5
  checkEq "nested CC" f2.cc 5
  -- Cognitive = for(+1, nest 0) + if(+2, nest 1) + if(+3, nest 2) + unless(+4, nest 3) = 10
  checkEq "nested cognitive" f2.cognitive 10
  check "nested cognitive exceeds CC" (f2.cognitive > f2.cc)

  -- 3. Chained `else if` stays flat in Cognitive Complexity (+1 per else-if, no nesting blowup)
  let chainCode := "
def grade (n : Nat) : String :=
  if n >= 90 then \"A\"
  else if n >= 80 then \"B\"
  else if n >= 70 then \"C\"
  else \"F\"
"
  let r3 ← instrumentSource env "Chain.lean" chainCode 0 { analyzeOnly := true }
  let f3 := r3.functions[0]!
  checkEq "else-if chain CC" f3.cc 4
  checkEq "else-if chain cognitive" f3.cognitive 3

  -- 4. Boolean operator transitions: `a && b && c` adds +1 cog, `a && b || c` adds +2 cog
  let boolCode := "
def sameOp (a b c : Bool) : Bool := a && b && c
def mixedOp (a b c : Bool) : Bool := (a && b) || c
"
  let r4 ← instrumentSource env "Bool.lean" boolCode 0 { analyzeOnly := true }
  checkEq "sameOp cognitive" r4.functions[0]!.cognitive 1
  checkEq "sameOp CC" r4.functions[0]!.cc 3
  checkEq "mixedOp cognitive" r4.functions[1]!.cognitive 2
  checkEq "mixedOp CC" r4.functions[1]!.cc 3

private unsafe def testInstrumentAndCompile : TM Unit := do
  let env ← loadParserEnv
  -- Tricky Lean syntax covering every instrumented construct
  let sample := "
namespace Demo

def straight (x : Nat) : Nat := x + 1

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

instance : ToString Bool where
  toString b := if b then \"yes\" else \"no\"

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

end Demo
"
  let res ← instrumentSource env "Demo.lean" sample 0 {}
  checkEq "no parse skip" res.skippedReason none
  check "recorded functions" (res.functions.size ≥ 7)
  check "recorded sites" (res.sites.size ≥ 20)
  check "injected DoSyntax import" ((res.instrumented.splitOn "import LeanCov.DoSyntax").length > 1)
  -- Compile the instrumented source with `lake env lean` to prove it typechecks cleanly!
  let tmpPath : System.FilePath := ".lake/build/tmp_instrument_check.lean"
  if let some p := tmpPath.parent then IO.FS.createDirAll p
  IO.FS.writeFile tmpPath res.instrumented
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", tmpPath.toString] }
  let _ ← IO.Process.output { cmd := "rm", args := #["-f", tmpPath.toString] }
  check s!"instrumented code typechecks" (out.exitCode == 0) s!"{out.stdout}{out.stderr}"

private def testProfilesAndReports : TM Unit := do
  let dir : System.FilePath := ".lake/build/tmp_prof_test"
  IO.FS.createDirAll dir
  let p1 := dir / "a.cov"
  let p2 := dir / "b.cov"
  initProfile p1 4
  initProfile p2 4
  let h0 ← readProfile p1
  checkEq "fresh profile zeroed" h0 #[0, 0, 0, 0]
  -- Write non-zero counts into p1 and p2
  let mkProf (vals : Array UInt64) : ByteArray := Id.run do
    let mut b := profileMagic
    let pushU64 (acc : ByteArray) (v : UInt64) : ByteArray := Id.run do
      let mut out := acc
      for i in [:8] do out := out.push ((v >>> (i * 8).toUInt64) &&& 0xFF).toUInt8
      return out
    b := pushU64 b vals.size.toUInt64
    for v in vals do b := pushU64 b v
    return b
  IO.FS.writeBinFile p1 (mkProf #[3, 0, 1, 0])
  IO.FS.writeBinFile p2 (mkProf #[2, 5, 0, 0])
  let merged ← mergeProfiles #[p1, p2] 4
  checkEq "merged profile sums" merged #[5, 5, 1, 0]

  -- Build a synthetic manifest and verify CRAP, Cognitive CRAP, and LCOV output
  let manifest : Manifest := {
    sites := #[
      { id := 0, file := "Foo.lean", decl := "Foo.bar", line := 10, col := 3, kind := .ifThen },
      { id := 1, file := "Foo.lean", decl := "Foo.bar", line := 11, col := 3, kind := .ifElse },
      { id := 2, file := "Foo.lean", decl := "Foo.baz", line := 20, col := 3, kind := .matchArm },
      { id := 3, file := "Foo.lean", decl := "Foo.baz", line := 21, col := 3, kind := .matchArm }
    ]
    functions := #[
      { name := "Foo.bar", file := "Foo.lean", line := 9, endLine := 12, lines := 4, cc := 2, cognitive := 1, siteIds := #[0, 1] },
      { name := "Foo.baz", file := "Foo.lean", line := 19, endLine := 22, lines := 4, cc := 10, cognitive := 2, siteIds := #[2, 3] }
    ]
  }
  let rep := buildReport manifest merged
  checkEq "total sites" rep.sitesTotal 4
  checkEq "hit sites" rep.sitesHit 3
  checkEq "functions hit" rep.functionsHit 2
  -- Foo.bar has 2/2 covered (cov=1.0) -> CRAP = 2.0, CogCRAP = 1.0
  check "Foo.bar CRAP == 2.0" (rep.functions[0]!.crap == 2.0)
  check "Foo.bar CogCRAP == 1.0" (rep.functions[0]!.cogCrap == 1.0)
  -- Foo.baz has 1/2 covered (cov=0.5) -> CRAP = 100 * 0.125 + 10 = 22.5, CogCRAP = 4 * 0.125 + 2 = 2.5
  check "Foo.baz CRAP == 22.5" (rep.functions[1]!.crap == 22.5)
  check "Foo.baz CogCRAP == 2.5" (rep.functions[1]!.cogCrap == 2.5)
  checkEq "Foo.baz uncovered line" rep.functions[1]!.uncoveredLines #[21]

  let lcov := toLcov manifest merged
  check "LCOV has SF" ((lcov.splitOn "SF:Foo.lean").length > 1)
  check "LCOV has BRF:4" ((lcov.splitOn "BRF:4").length > 1)
  check "LCOV has BRH:3" ((lcov.splitOn "BRH:3").length > 1)
  check "LCOV has end_of_record" ((lcov.splitOn "end_of_record").length > 1)

  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir.toString] }

unsafe def main : IO UInt32 :=
  runMain "leancov-test" do
    runTest "complexity (CC vs Cognitive)" testComplexity
    runTest "AST instrumentation & typecheck" testInstrumentAndCompile
    runTest "binary profiles, CRAP & LCOV" testProfilesAndReports
