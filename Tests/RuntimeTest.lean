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

-- Verify `@[expose, reducible]` probe transparency to kernel `rfl`
theorem structLen_nil : structLen [] = 0 := rfl
theorem cond_transparent (b : Bool) : LeanCov.cond 1 2 b = b := rfl
theorem pass_transparent (x : Nat) : LeanCov.pass 1 x = x := rfl
theorem mark_transparent : LeanCov.mark 1 = true := rfl

private def catchesRT (act : IO α) : IO Bool :=
  try let _ ← act; pure false catch _ => pure true

private def checkHarness : TM Unit := do
  LeanCov.raiseStack ()
  check "basic truth" (1 + 1 == 2)
  checkEq "pureProbeId(0)" (pureProbeId 0) 42
  checkEq "pureProbeId(4)" (pureProbeId 4) (4 + 0 + 2)
  checkEq "structLen" (structLen [10, 20, 30]) 3
  let _ := LeanCov.pass 8 123
  let _ := LeanCov.mark 9
  let v ← need "ok except" (Except.ok 99 : Except String Nat)
  checkEq "need unwrapped" v 99
  let vt ← need "ok exceptT" (pure 77 : ExceptT String IO Nat)
  checkEq "need exceptT" vt 77
  check "need throws on error" (← catchesRT (need "bad" (Except.error "err" : Except String Nat)))
  let e ← needE "ok custom" id (Except.ok "hi" : Except String String)
  checkEq "needE unwrapped" e "hi"
  check "needE throws on error" (← catchesRT (needE "badE" unnamed (Except.error "err" : Except String Nat)))
  refused "expected error" (Except.error "boom" : Except String Nat) (kind := "boom")
  refused "expected error any kind" (Except.error "boom" : Except String Nat)

  -- Exercise progressLines, failure recording, refused mismatch, and runTest filtering/abort paths,
  -- then restore global tally/flags so the suite exits cleanly with 0 failures.
  let savedTally ← tally.get
  progressLines.set true
  check "progress with detail" true "all good"
  check "synthetic fail" false "expected"
  refused "synthetic unexpected ok" (Except.ok 1 : Except String Nat)
  refused "synthetic wrong kind" (Except.error "boom" : Except String Nat) (kind := "other")
  refused "synthetic pred false" (Except.error "boom" : Except String Nat) (kind := "boom") (matching := fun _ => false)
  progressLines.set false
  onlyTests.set (some "run_target")
  runTest "skipped_case" (pure ())
  runTest "run_target_tm_err" (throw "tm abort")
  runTest "run_target_io_err" (liftM (throw (IO.userError "io abort") : IO Unit))
  onlyTests.set none
  let tempTally ← tally.get
  tally.set savedTally
  check "synthetic failures were recorded before restore" (tempTally.failures.size ≥ 5)

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
  LeanCov.fuzzReset ()
  let v0 ← IO.monoMsNow
  let pv := LeanCov.pass 500 v0
  let e1 ← LeanCov.fuzzCheckNew ()
  let e0 ← LeanCov.fuzzCheckNew ()
  let mut acc : Nat := 0
  for i in [:4] do
    acc := acc + LeanCov.hit 501 fun () => i + 1
  let e501a ← LeanCov.fuzzCheckNew ()
  let mut acc2 : Nat := 0
  for i in [:4] do
    acc2 := acc2 + LeanCov.hit 501 fun () => i + 10
  let e501b ← LeanCov.fuzzCheckNew ()
  let covSites ← LeanCov.fuzzCoveredSites ()
  checkEq "pass site 500 preserves value" pv v0
  check "fuzzCheckNew sees first hit" (e1.toNat ≥ 1)
  checkEq "fuzzCheckNew sees 0 on idle check" e0.toNat 0
  checkEq "hit 501 loop sum" acc 10
  checkEq "hit 501 loop2 sum" acc2 46
  checkEq "fuzzCheckNew detects site 501 AFL bucket" e501a.toNat 1
  checkEq "fuzzCheckNew ignores same AFL bucket" e501b.toNat 0
  check "fuzzCoveredSites tracks >= 2 sites" (covSites.toNat ≥ 2)

def main : IO UInt32 :=
  runMain "leancov-rt-test" do
    runTest "check harness & runtime probes" checkHarness
    runTest "fuzz primitives" checkFuzzPrimitives
