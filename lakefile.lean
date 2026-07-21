import Lake

open Lake DSL

-- Keep the package and root-module names aligned for external declaration checkers.
package FreeRange where
  version := v!"0.1.0"
  description := "Proof-backed ergonomic range analysis for pure Lean 4 programs"
  license := "MIT"

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
