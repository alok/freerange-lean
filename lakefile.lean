import Lake

open Lake DSL

package freerange where
  version := v!"0.1.0"
  description := "Proof-backed ergonomic range analysis for pure Lean 4 programs"
  license := "MIT"

lean_lib FreeRange

@[default_target]
lean_exe freerange where
  root := `Main

lean_lib Tests where
  roots := #[`Test.Range, `Test.Expr, `Test.Analyze, `Test.Soundness]

@[test_driver]
lean_exe tests where
  root := `Test.Main
