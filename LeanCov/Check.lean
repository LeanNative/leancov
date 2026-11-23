/-! # Lightweight test runner (`LeanCov.Check`)

One tally per process (`check`, `fail`, `need`, `needE`, `refused`, `runTest`, `runMain`):
- failures print immediately to stdout (`  FAIL name — detail`), flushed;
- passes stay quiet unless `progress := true`;
- `<EXE>_ONLY=<substring>` filters `runTest` cases;
- `runMain` prints `<exe>: P passed, F failed[: names]` and exits cleanly via `IO.Process.exit`
  (so background tasks in tested code cannot hang process shutdown). -/

namespace LeanCov.Check

structure Tally where
  passed : Nat := 0
  failures : Array String := #[]
  deriving Inhabited

initialize tally : IO.Ref Tally ← IO.mkRef {}
initialize progressLines : IO.Ref Bool ← IO.mkRef false
initialize onlyTests : IO.Ref (Option String) ← IO.mkRef none

/-- Print a flushed line to stdout. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

private def formatLine (mark name detail : String) : String :=
  s!"  {mark} {name}{if detail.isEmpty then "" else " — " ++ detail}"

/-- Record a test failure with optional detail. -/
def fail (name : String) (detail : String := "") : IO Unit := do
  tally.modify fun t => { t with failures := t.failures.push name }
  say (formatLine "FAIL" name detail)

/-- Record a boolean assertion. -/
def check (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    tally.modify fun t => { t with passed := t.passed + 1 }
    if ← progressLines.get then say (formatLine "ok  " name detail)
  else fail name detail

/-- Assert equality, showing expected vs. actual on failure. -/
def checkEq [BEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  check name (actual == expected) s!"got {reprStr actual}, expected {reprStr expected}"

/-! ## Error unwrapping -/

/-- Describes an error type by its case name (for `refused`) and human-readable text. -/
class Describe (ε : Type) where
  name : ε → String
  describe : ε → String := name

instance : Describe String := ⟨id, id⟩

/-- Lifts `Except ε` or `ExceptT ε IO` into `IO (Except ε α)`. -/
class Outcome (m : Type → Type) (ε : outParam Type) where
  outcome {α : Type} : m α → IO (Except ε α)

instance : Outcome (Except ε) ε := ⟨fun r => pure r⟩
instance : Outcome (ExceptT ε IO) ε := ⟨ExceptT.run⟩

/-- Unwrap an `Outcome` or abort the current `runTest` with `name: <error>`. -/
def need {m ε α n} [Outcome m ε] [Describe ε] [MonadLiftT IO n] (name : String) (x : m α) : n α :=
  liftM (m := IO) do
    match ← Outcome.outcome x with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{name}: {Describe.describe e}")

/-- Unwrap an `Except ε α` using a custom formatter. -/
def needE {ε α n} [MonadLiftT IO n] (name : String) (render : ε → String) (r : Except ε α) : n α :=
  liftM (m := IO) do
    match r with
    | .ok a => pure a
    | .error e => throw (IO.userError s!"{name}: {render e}")

/-- Default error renderer when details are not needed. -/
def unnamed {ε} (_ : ε) : String := "failed"

/-- Assert that an `Outcome` fails, optionally matching its error case name and predicate. -/
def refused {m ε α} [Outcome m ε] [Describe ε] (name : String) (x : m α) (kind : String := "")
    (matching : ε → Bool := fun _ => true) : IO Unit := do
  match ← Outcome.outcome x with
  | .ok _ => check name false "accepted"
  | .error e =>
    check name ((kind.isEmpty || Describe.name e == kind) && matching e) s!"got {Describe.describe e}"

/-! ## Test cases and main entry point -/

/-- A test body that may abort by throwing a `String` message or `IO.Error`. -/
abbrev TM := ExceptT String IO

/-- Run a named test case (respecting `<EXE>_ONLY`), recording aborts as failures and timing it. -/
def runTest (name : String) (t : TM Unit) : IO Unit := do
  if let some only ← onlyTests.get then
    unless (name.splitOn only).length > 1 do return
  let start ← IO.monoMsNow
  match ← (try t.run catch e => pure (.error (toString e))) with
  | .ok () => pure ()
  | .error msg => fail name s!"aborted: {msg}"
  say s!"  {name}: {(← IO.monoMsNow) - start} ms"

/-- Entry point for a test executable. Prints a summary and exits 0 on pass or 1 on failure. -/
def runMain (exe : String) (body : IO Unit) (progress := false) : IO UInt32 := do
  progressLines.set progress
  let var := (exe.map fun c => if c == '-' then '_' else c.toUpper) ++ "_ONLY"
  onlyTests.set (← IO.getEnv var)
  try body catch e => fail "exception" (toString e)
  let t ← tally.get
  say s!"{exe}: {t.passed} passed, {t.failures.size} failed{if t.failures.isEmpty then "" else ": " ++ ", ".intercalate t.failures.toList}"
  IO.Process.exit (if t.failures.isEmpty then 0 else 1)

end LeanCov.Check
