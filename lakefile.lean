import Lake
open Lake DSL

package «leancov» where
  version := v!"0.5.0"
  description := "Source-level branch & line coverage, McCabe/Cognitive CRAP, AST mutation testing, and greybox fuzzing for Lean 4"
  keywords := #["coverage", "testing", "mutation-testing", "fuzzing", "crap", "lcov"]
  homepage := "https://github.com/LeanNative/leancov"
  license := "MIT"

target leancov_rt.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "leancov_rt.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "leancov_rt.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2", "-std=c11", "-Wall", "-Wextra"] "cc" getLeanTrace

extern_lib libleancov_rt pkg := do
  let name := nameToStaticLib "leancov_rt"
  let rtO ← leancov_rt.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[rtO]

/-- Lightweight test & fuzzing kit + runtime coverage probes (zero `Lean` runtime dependency). -/
lean_lib «LeanCov» where
  roots := #[`LeanCov.Runtime, `LeanCov.DoSyntax, `LeanCov.Check, `LeanCov.Fuzz]
  precompileModules := true

/-- Compiler/CLI library for source-level AST instrumentation, complexity analysis, and reporting. -/
lean_lib «LeanCovTool» where
  srcDir := "."
  roots := #[`LeanCov.Cov, `LeanCov.CLI]

@[default_target]
lean_exe «leancov» where
  root := `LeanCov.Main
  supportInterpreter := true

lean_exe «leancov-rt-test» where
  srcDir := "."
  root := `Tests.RuntimeTest

lean_exe «leancov-fuzz-test» where
  srcDir := "."
  root := `Tests.FuzzTest

@[test_driver]
lean_exe «leancov-test» where
  srcDir := "."
  root := `Tests.SelfTest
  supportInterpreter := true
