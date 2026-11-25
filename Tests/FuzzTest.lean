import LeanCov.Fuzz

/-! # End-to-end fuzz supervisor test executable (`leancov-fuzz-test`)

Exercises `LeanCov.Fuzz.main` (parent supervisor, child `LEAN_ABORT_ON_PANIC=1`, corpus replay,
`--target`, `--seed`, `--iterations`, `--max-input`, `--save`, and intentional finding detection). -/

private def cleanTarget : LeanCov.Fuzz.Target := {
  name := "clean"
  seeds := #["hello".toUTF8, "123".toUTF8]
  tokens := #["!".toUTF8, " ".toUTF8]
  check := fun _ input => do
    LeanCov.Fuzz.require (input.size ≤ 65536) "size bound"
    return !input.isEmpty
}

private def findingTarget : LeanCov.Fuzz.Target := {
  name := "finding"
  seeds := #["ok".toUTF8]
  check := fun _ input => do
    if input.size > 3 then throw (IO.userError "intentional finding")
    return true
}

private def noSeedTarget : LeanCov.Fuzz.Target := {
  name := "noseed"
  seeds := #["ignored".toUTF8]
  check := fun _ _ => return false
}

private def guidedTarget : LeanCov.Fuzz.Target := {
  name := "guided"
  seeds := #["ab".toUTF8]
  tokens := #["!".toUTF8, "x".toUTF8]
  check := fun _ input => do
    if input.size ≥ 2 && input[0]! == 'a'.toUInt8 && input[1]! == 'b'.toUInt8 then
      if input.size ≥ 3 && input[2]! == '!'.toUInt8 then
        let hit := LeanCov.hit 700 fun () => (1 : Nat)
        if input.size ≥ 4 && input[3]! == 'x'.toUInt8 then
          let hit2 := LeanCov.hit 701 fun () => hit + 1
          return hit2 > 0
        return hit > 0
      return true
    return false
}

def main (args : List String) : IO UInt32 := do
  let corpus? := (← IO.getEnv "LEANCOV_TEST_CORPUS").map System.FilePath.mk
  LeanCov.Fuzz.main #[cleanTarget, findingTarget, noSeedTarget, guidedTarget] args (corpus := corpus?)
