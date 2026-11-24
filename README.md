# leancov

Source-level branch & line coverage, McCabe CRAP, SonarSource-style Cognitive Complexity, and a lightweight test/fuzzing kit for Lean 4.

Unlike C-level (`clang -fprofile-instr-generate`) coverage over Lean's generated C, `leancov` parses `.lean` files with Lean's own parser, injects minimal source-level probes into a staged out-of-tree copy, and records branch hits via a tiny POSIX C `mmap(MAP_SHARED)` runtime. That means:

- **Zero C codegen noise & zero startup inflation** — no reference-counting reuse checks (`isShared`), monad bind plumbing, boxed trampolines, or inlined-away functions; pure 0-arg constants/CAFs are excluded, `leancov stage` arms `def main` with `LEAN_COV_DEFER_INIT=1` so module initializers produce 0.0% startup coverage, and `@[never_extract]` prevents Lean's compiler from hoisting constant-returning probes into `lean_once_cell_t` caches.
- **Strict branch vs. function separation** — top-level branch coverage and LCOV `BRDA`/`BRF`/`BRH` count only genuine control-flow and boolean-operand outcomes (including `for`/`while` 0-iteration `loop.skip` and terminal `&&`/`||` RHS operands), never straight-line `fn.entry` probes.
- **Crash- and `SIGKILL`-safe counters** — atomic 64-bit increments directly into a shared memory-mapped `.cov` file survive panics, multi-process tests, and killed child processes.
- **No `Lean` runtime dependency in tested binaries** — `LeanCov.Runtime` has zero `Lean` imports, and `LeanCov.DoSyntax` uses `public meta import Lean` so instrumented executables link cleanly without `supportInterpreter := true`.
- **Kernel & recursion compatible** — probes elaborate eagerly preserving `expectedType?`, metavariable order, `let mut`/`return`/`continue`/`break`, `Prop` erasure, `termination_by`, and structural recursion (`brecOn`).
- **McCabe CRAP + Cognitive CRAP** — alongside classic `CRAP = CC²·(1-cov)³ + CC`, `leancov` computes nesting-weighted Cognitive Complexity (`CogCRAP = Cog²·(1-cov)³ + Cog`) so flat `match` tables stay low while deeply nested untested logic surfaces first.
- **Standard outputs** — terminal tables, machine-readable JSON, and standard **LCOV** (`.info`) for `genhtml`, Codecov, Coveralls, and IDE gutters.

## Requirements

- **Lean 4** installed via [`elan`](https://github.com/leanprover/elan) (tested with the version pinned in [`lean-toolchain`](lean-toolchain))
- **macOS or Linux** with a C compiler (`cc`) for `libleancov_rt` (POSIX `mmap(MAP_SHARED)` runtime)

## Modules

`leancov` ships as a single Lake package with opt-in modules:

| Module | Purpose | `Lean` runtime dep? |
|---|---|---|
| `LeanCov.Check` | Minimal test harness (`check`, `checkEq`, `fail`, `need`, `needE`, `refused`, `runTest`, `runMain`, `<EXE>_ONLY`) | None |
| `LeanCov.Fuzz` | Deterministic SplitMix64 mutation fuzzer with `LEAN_ABORT_ON_PANIC=1` supervision, stall watchdog, and corpus replay | None |
| `LeanCov.Runtime` | `@[extern]` probe primitives backed by `c/leancov_rt.c` (`libleancov_rt`) | None |
| `LeanCov.DoSyntax` | Eager `leancov_hit%` (`doElem`) and `leancov_term%` (`term`) elaborators | Meta-only (`public meta import Lean`) |
| `LeanCov.Cov` | AST complexity analyzer, byte-offset instrumenter, binary `.cov` I/O, JSON & LCOV reporter | Compiler/CLI only |
| `leancov` CLI | Standalone CLI (`stage`, `instrument`, `run`, `report`, `analyze`, `--version`) | CLI binary |

## Installation

### 1. Add as a Lake Dependency (for `LeanCov.Check`, `LeanCov.Fuzz`, or `lake exe leancov`)

**`lakefile.toml` (git dependency):**

```toml
[[require]]
name = "leancov"
git = "https://github.com/<org>/leancov"
rev = "main" # or pin to a release tag / commit SHA
```

**`lakefile.lean` (git dependency):**

```lean
require leancov from git
  "https://github.com/<org>/leancov" @ "main"
```

For a local checkout or monorepo, use a path dependency instead:

```toml
[[require]]
name = "leancov"
path = "../leancov"
```

```lean
require leancov from "../leancov"
```

Then fetch and build from your project:

```sh
lake update leancov
lake build leancov
lake exe leancov --version
```

### 2. Install the Standalone `leancov` CLI on `PATH`

If you want to run `leancov` across any Lean project without adding it to every `lakefile`:

```sh
git clone https://github.com/<org>/leancov
cd leancov
lake build leancov

# Option A: symlink into a directory already on your PATH (recommended — preserves toolchain lookup)
mkdir -p ~/.local/bin
ln -sf "$(pwd)/.lake/build/bin/leancov" ~/.local/bin/leancov

# Option B: add leancov's bin directory to PATH in your shell profile (~/.zshrc or ~/.bashrc)
export PATH="$(pwd)/.lake/build/bin:$PATH"

# Verify installation
leancov --version   # prints: leancov 0.1.0
```

> **Note on toolchain lookup:** `leancov` walks up from its resolved executable path to find its own `lean-toolchain` and Lean sysroot, so symlinking `.lake/build/bin/leancov` works from any working directory. If you copy the binary out of the checkout, set `LEAN_SYSROOT="$(lean --print-prefix)"`.

## CLI Workflow

### 1. Static Complexity Analysis (`analyze`)

Measure McCabe Cyclomatic Complexity and Cognitive Complexity directly from Lean source without building or running tests:

```sh
leancov analyze \
  --src MyLib \
  --exclude Proofs/ \
  --sort cog \
  --top 25 \
  --json build/complexity.json
```

Use `--sort cc` to sort by McCabe CC instead of Cognitive Complexity. Pass `--imports Mod1,Mod2` if your files use custom syntax defined in another built module.

### 2. Stage an Instrumented Copy (`stage`)

`leancov stage` creates an out-of-tree instrumented copy of a Lake package (never modifying your working tree), rewrites relative dependency paths in `lakefile.toml` / `lakefile.lean` / `lake-manifest.json`, symlinks `.lake/packages/*` for fast offline builds, arms top-level `def main` entry points, and emits `sites.json`:

```sh
leancov stage \
  --pkg . \
  --out build/leancov-stage \
  --leancov /path/to/leancov \
  --exclude Proofs/ --exclude Tests/
```

If `leancov` is already a Lake dependency of your project, point `--leancov` at `.lake/packages/leancov`. Use `--src-dir <relDir>` (repeatable) to select specific source directories instead of auto-discovering all directories containing `.lean` files.

Build your test executables inside the staged copy:

```sh
(cd build/leancov-stage && lake build my-tests)
```

### 3. Run Instrumented Binaries (`run`)

`leancov run` initializes the `.cov` profile file, sets `LEAN_COV_FILE`, `LEAN_COV_SITES`, and `LEAN_COV_DEFER_INIT=1` (when `sites.json` has armed `main` entry points), and runs your test command:

```sh
leancov run \
  --sites build/leancov-stage/sites.json \
  --profile build/leancov-stage/profiles/unit.cov \
  -- build/leancov-stage/.lake/build/bin/my-tests
```

Pass `--append` to accumulate multiple runs into the same `.cov` file, or save separate `.cov` files into a directory and merge them with `--profile-dir` at report time. Use `--no-defer-init` to include module-initializer hits.

### 4. Report Coverage, CRAP, JSON & LCOV (`report`)

Merge one or more `.cov` profiles, print summary tables, and export machine-readable JSON and LCOV:

```sh
leancov report \
  --sites build/leancov-stage/sites.json \
  --profile-dir build/leancov-stage/profiles \
  --sort cog --files --kinds --missed --top 25 \
  --json build/leancov-stage/coverage.json \
  --lcov build/leancov-stage/lcov.info
```

Sort modes: `--sort crap` (McCabe CRAP, default), `--sort cog` (Cognitive CRAP), `--sort cc` (McCabe CC), or `--sort uncov` (uncovered branch count). Generate browsable HTML from LCOV with `genhtml build/leancov-stage/lcov.info -o build/html`.

### Multi-Package Workspaces

Use `--prefix`, `--dep <name>=<stagedPath>`, and `--append-sites` to share one unified `sites.json` and `.cov` counter space across dependent Lake packages:

```sh
leancov stage --pkg Core --out build/stage/Core --leancov /path/to/leancov \
  --prefix Core --sites build/stage/sites.json --exclude Proofs/

leancov stage --pkg App --out build/stage/App --leancov /path/to/leancov \
  --prefix App --dep core=build/stage/Core \
  --sites build/stage/sites.json --append-sites --exclude Tests/
```

## CI Quality Gates

`leancov report` exits with code `1` if any configured threshold is breached:

```sh
leancov report \
  --sites build/leancov-stage/sites.json \
  --profile-dir build/leancov-stage/profiles \
  --files --kinds --sort cog --top 20 \
  --lcov build/leancov-stage/lcov.info \
  --min-cov 75.0 \
  --max-crap 100.0 \
  --max-cog-crap 200.0
```

Example GitHub Actions step:

```yaml
- name: Coverage & quality gates
  run: |
    leancov stage --pkg . --out build/stage --leancov .lake/packages/leancov --exclude Proofs/
    (cd build/stage && lake build my-tests)
    leancov run --sites build/stage/sites.json --profile build/stage/tests.cov \
      -- build/stage/.lake/build/bin/my-tests
    leancov report --sites build/stage/sites.json --profile build/stage/tests.cov \
      --files --kinds --sort cog --top 20 \
      --lcov build/stage/lcov.info \
      --min-cov 75.0 --max-crap 100.0 --max-cog-crap 200.0
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
  LeanCov.Fuzz.main #[myTarget] args (corpus := some "Corpus")
```

## Instrumented Constructs

| Lean construct | Probes recorded |
|---|---|
| `if c then t else e`, `if h : c`, `if let p := e` | `if.then`, `if.else` (including implicit fallthrough of one-armed `do` `if`) |
| `unless c do body` | `unless.enter`, `unless.skip` |
| `match` / pattern equations / `doMatch` | `match.arm` per arm |
| `let p := e \| fallback` & `let p ← act \| fallback` | `letElse.ok`, `letElse.fail` |
| `for`, `while` / `repeat` | `loop.body` + `loop.skip` (0 iterations) / `loop.body` |
| `try ... catch` | `catch.body` |
| `a && b`, `a \|\| b` (disable with `--no-bool-ops`) | `and.true`/`and.false`, `or.true`/`or.false` on every atomic operand (both LHS and RHS) |
| Callable straight-line functions (0 branches, excludes pure 0-arg constants) | `fn.entry` (counted in function & line coverage, excluded from branch coverage) |

## Runtime Environment Variables

- `LEAN_COV_FILE` — path to the binary `.cov` file (`%p` expands to the process PID; without `%p`, parent and child processes share one file atomically).
- `LEAN_COV_SITES` — site count used if the runtime initializes a new `.cov` file directly.
- `LEAN_COV_DEFER_INIT` — when `1` (set automatically by `leancov run` when `sites.json` has `armOnMain: true`), suppresses hits fired during module initialization until `LeanCov.arm ()` runs at `main` entry.

When `LEAN_COV_FILE` is unset, every probe is a single null-pointer check.

## Self-Tests & Self-Coverage

```sh
lake build leancov leancov-rt-test leancov-test leancov-fuzz-test
.lake/build/bin/leancov --version
.lake/build/bin/leancov-rt-test
.lake/build/bin/leancov-test
```

Run a self-coverage dogfood pass on `leancov` itself:

```sh
.lake/build/bin/leancov stage --pkg . --out build/self-stage --self \
  --src-dir LeanCov --exclude Runtime.lean --exclude DoSyntax.lean --exclude Main.lean
(cd build/self-stage && lake build leancov leancov-rt-test leancov-fuzz-test leancov-test)
.lake/build/bin/leancov run --sites build/self-stage/sites.json --profile build/self-stage/self.cov \
  -- build/self-stage/.lake/build/bin/leancov-rt-test
.lake/build/bin/leancov run --sites build/self-stage/sites.json --profile build/self-stage/self.cov --append \
  -- build/self-stage/.lake/build/bin/leancov-test
.lake/build/bin/leancov report --sites build/self-stage/sites.json --profile build/self-stage/self.cov \
  --files --kinds --sort cog --top 10
rm -rf build/self-stage
```

## License

MIT — see [`LICENSE`](LICENSE).
