import Lake

open Lake DSL

-- Keep the package and root-module names aligned for external declaration checkers.
package FreeRange where
  version := v!"0.3.0"
  description := "Proof-backed range analysis for embedded exact-Int expressions"
  license := "MIT"
  builtinLint := true
  restoreAllArtifacts := true

lean_lib FreeRange

@[default_target]
lean_exe freerange where
  root := `Main

lean_lib Tests where
  roots := #[`Test.Range, `Test.Expr, `Test.Analyze, `Test.Soundness, `Test.Report,
    `Test.Axioms, `Test.Quickstart]

@[test_driver]
lean_exe tests where
  root := `Test.Main
