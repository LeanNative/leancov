# leancov

Source-level branch & line coverage, McCabe CRAP, SonarSource-style Cognitive Complexity, and a lightweight test/fuzzing kit for Lean 4.

Unlike C-level (`clang -fprofile-instr-generate`) coverage over Lean's generated C, `leancov` parses `.lean` files with Lean's own parser, injects minimal source-level probes into a staged out-of-tree copy, and records branch hits via a tiny POSIX C `mmap(MAP_SHARED)` runtime. That means:

- **Zero C codegen noise** — no reference-counting reuse checks (`isShared`), monad bind plumbing, boxed trampolines, or inlined-away functions.
- **Crash- and `SIGKILL`-safe counters** — atomic 64-bit increments directly into a shared memory-mapped `.cov` file survive panics, multi-process tests, and killed child processes.
- **No `Lean` runtime dependency in tested binaries** — `LeanCov.Runtime` has zero `Lean` imports, and `LeanCov.DoSyntax` uses `public meta import Lean` so instrumented executables link cleanly without `supportInterpreter := true`.
- **Kernel & recursion compatible** — probes elaborate eagerly preserving `expectedType?`, metavariable order, `let mut`/`return`/`continue`/`break`, `Prop` erasure, `termination_by`, and structural recursion (`brecOn`).
- **McCabe CRAP + Cognitive CRAP** — alongside classic `CRAP = CC²·(1-cov)³ + CC`, `leancov` computes nesting-weighted Cognitive Complexity (`CogCRAP = Cog²·(1-cov)³ + Cog`) so flat `match` tables stay low while deeply nested untested logic surfaces first.
- **Standard outputs** — terminal tables, machine-readable JSON, and standard **LCOV** (`.info`) for `genhtml`, Codecov, Coveralls, and IDE gutters.

## Modules

`leancov` ships as a single Lake package with opt-in modules:

| Module | Purpose | `Lean` runtime dep? |
|---|---|---|
| `LeanCov.Check` | Minimal test harness (`check`, `checkEq`, `fail`, `need`, `needE`, `refused`, `runTest`, `runMain`, `<EXE>_ONLY`) | None |
| `LeanCov.Fuzz` | Deterministic SplitMix64 mutation fuzzer with `LEAN_ABORT_ON_PANIC=1` supervision, stall watchdog, and corpus replay | None |
| `LeanCov.Runtime` | `@[extern]` probe primitives backed by `c/leancov_rt.c` (`libleancov_rt`) | None |
| `LeanCov.DoSyntax` | Eager `leancov_hit%` (`doElem`) and `leancov_term%` (`term`) elaborators | Meta-only (`public meta import Lean`) |
| `LeanCov.Cov` | AST complexity analyzer, byte-offset instrumenter, binary `.cov` I/O, JSON & LCOV reporter | Compiler/CLI only |
| `lake exe leancov` | Standalone CLI (`stage`, `instrument`, `run`, `report`, `analyze`) | CLI binary |

## Installation

### `lakefile.toml`

```toml
[[require]]
name = "leancov"
path = "../leancov" # or git = "...", rev = "..."
```

### `lakefile.lean`

```lean
require leancov from "../leancov"
```

Then build the CLI once:

```sh
lake build leancov
```

## CLI Quickstart

### 1. Static Complexity Analysis (no build or tests required)

```sh
leancov analyze --src MyLib --exclude Proofs/ --top 25 --sort cog
```

### 2. Stage, Build, Run, and Report Coverage

`leancov stage` creates an instrumented out-of-tree copy of a Lake package (without modifying your repository), reuses existing `.lake/packages/*` via symlinks, and emits `sites.json`:

```sh
# Stage an instrumented copy
leancov stage \
  --pkg . \
  --out build/leancov-stage \
  --leancov /path/to/leancov \
  --exclude Proofs/ --exclude Tests/

# Build your test binaries in the staged copy
(cd build/leancov-stage && lake build my-tests)

# Run tests with coverage recording
leancov run \
  --sites build/leancov-stage/sites.json \
  --profile build/leancov-stage/my-tests.cov \
  -- build/leancov-stage/.lake/build/bin/my-tests

# Print CRAP + Cognitive CRAP report and export JSON / LCOV
leancov report \
  --sites build/leancov-stage/sites.json \
  --profile build/leancov-stage/my-tests.cov \
  --sort cog --files --top 25 \
  --json build/leancov-stage/coverage.json \
  --lcov build/leancov-stage/lcov.info
```

### Multi-Package Workspaces

Use `--prefix`, `--dep <name>=<stagedPath>`, and `--append-sites` to share one unified `sites.json` and `.cov` counter space across dependent Lake packages:

```sh
leancov stage --pkg Core --out build/stage/Core --leancov /path/to/leancov \
  --prefix Core --sites build/stage/sites.json --exclude Proofs/

leancov stage --pkg App --out build/stage/App --leancov /path/to/leancov \
  --prefix App --dep core=build/stage/Core \
  --sites build/stage/sites.json --append-sites --exclude Tests/
```

### CI Quality Gates

`leancov report` exits with code `1` if any configured threshold is breached:

```sh
leancov report \
  --sites build/stage/sites.json \
  --profile-dir build/stage/profiles \
  --min-cov 75.0 \
  --max-crap 100.0 \
  --max-cog-crap 200.0
```

## Using `LeanCov.Check` and `LeanCov.Fuzz`

### Unit tests (`LeanCov.Check`)

```lean
import LeanCov.Check
open LeanCov.Check

def testMath : TM Unit := do
  check "addition" (2 + 2 == 4)
  checkEq "multiply" (6 * 7) 42
  let v ← need "parse" (Except.ok 10 : Except String Nat)
  checkEq "unwrapped" v 10
  refused "bad input" (Except.error "invalid" : Except String Nat) (kind := "invalid")

def main : IO UInt32 :=
  runMain "my-test" do
    runTest "math" testMath
```

Filter a single test case with `MY_TEST_ONLY=math`.

### Mutation fuzzing (`LeanCov.Fuzz`)

```lean
import LeanCov.Fuzz

def myTarget : LeanCov.Fuzz.Target := {
  name := "parser"
  seeds := #["hello".toUTF8]
  check := fun _ input => do
    -- call your parser, assert invariants with `LeanCov.Fuzz.require`, return `true` if accepted
    return !input.isEmpty
}

def main (args : List String) : IO UInt32 :=
  LeanCov.Fuzz.main "my-fuzz" #[myTarget] args (corpus := some "Corpus")
```

## Instrumented Constructs

| Lean construct | Probes recorded |
|---|---|
| `if c then t else e`, `if h : c`, `if let p := e` | `if.then`, `if.else` (including implicit fallthrough of one-armed `do` `if`) |
| `unless c do body` | `unless.enter`, `unless.skip` |
| `match` / pattern equations / `doMatch` | `match.arm` per arm |
| `let p := e \| fallback` & `let p ← act \| fallback` | `letElse.ok`, `letElse.fail` |
| `for`, `while`, `repeat` | `loop.body` |
| `try ... catch` | `catch.body` |
| `a && b`, `a \|\| b` (disable with `--no-bool-ops`) | `and.true`/`and.false`, `or.true`/`or.false` |
| Straight-line functions (0 branches) | `fn.entry` |

## Runtime Environment Variables

- `LEAN_COV_FILE` — path to the binary `.cov` file (`%p` expands to the process PID; without `%p`, parent and child processes share one file atomically).
- `LEAN_COV_SITES` — site count used if the runtime initializes a new `.cov` file directly.

When `LEAN_COV_FILE` is unset, every probe is a single null-pointer check.

## Self-Tests

```sh
lake build leancov leancov-rt-test leancov-test
.lake/build/bin/leancov-rt-test
.lake/build/bin/leancov-test
```
