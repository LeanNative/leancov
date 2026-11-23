import LeanCov.Check
import LeanCov.Fuzz
import LeanCov.DoSyntax

/-! # Lightweight runtime & probe self-test (zero `Lean` runtime dependency)

Verifies that a normal `lean_exe` without `supportInterpreter := true` links cleanly against
`LeanCov.Runtime`, `LeanCov.DoSyntax`, `LeanCov.Check`, `LeanCov.Fuzz`, and `libleancov_rt`,
and that probes execute cleanly in `Id.run do`, `Except`, `IO`, and structural recursion. -/

open LeanCov.Check

private def pureProbeId (x : Nat) : Nat := Id.run do
  let mut acc := 0
  if x > 0 then
    leancov_hit% 0
    acc := acc + x
  else
    leancov_hit% 1
    acc := 42
  for i in [:x] do
    leancov_hit% 2
    if LeanCov.cond 3 4 (i % 2 == 0) && i < 10 then
      leancov_hit% 5
      acc := acc + i
  return acc

private def structLen : List Nat → Nat
  | [] => LeanCov.hit 6 fun () => 0
  | _ :: xs => LeanCov.hit 7 fun () => 1 + structLen xs
termination_by structural x => x

private def checkHarness : TM Unit := do
  check "basic truth" (1 + 1 == 2)
  checkEq "pureProbeId(0)" (pureProbeId 0) 42
  checkEq "pureProbeId(4)" (pureProbeId 4) (4 + 0 + 2)
  checkEq "structLen" (structLen [10, 20, 30]) 3
  let v ← need "ok except" (Except.ok 99 : Except String Nat)
  checkEq "need unwrapped" v 99
  let e ← needE "ok custom" id (Except.ok "hi" : Except String String)
  checkEq "needE unwrapped" e "hi"
  refused "expected error" (Except.error "boom" : Except String Nat) (kind := "boom")

private def checkFuzzPrimitives : TM Unit := do
  let r1 ← IO.mkRef (12345 : UInt64)
  let r2 ← IO.mkRef (12345 : UInt64)
  let a1 ← LeanCov.Fuzz.next r1
  let a2 ← LeanCov.Fuzz.next r2
  checkEq "SplitMix64 deterministic value" a1 a2
  checkEq "SplitMix64 deterministic state" (← r1.get) (← r2.get)
  let base := "hello world!".toUTF8
  let m1 ← LeanCov.Fuzz.mutate base r1 64
  let m2 ← LeanCov.Fuzz.mutate base r2 64
  check "mutate deterministic" (m1 == m2)
  check "mutate produces bounded output" (m1.size ≤ 64)
  let me ← LeanCov.Fuzz.mutate ByteArray.empty r1 32 #["tok".toUTF8]
  check "mutate empty bounded" (me.size ≤ 32)

def main : IO UInt32 :=
  runMain "leancov-rt-test" do
    runTest "check harness & runtime probes" checkHarness
    runTest "fuzz primitives" checkFuzzPrimitives
