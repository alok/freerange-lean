# Repository instructions

This repository implements Linear issues `ALOK-796` and `ALOK-800`: the proof-backed,
pure Lean 4 range analyzer and its release-grade polish pass.

Read `SPEC.md`, `POLISH_SPEC.md`, and `SEMANTICS.md` before changing behavior. The
specification’s exact-integer boundary is part of the public contract. Do not describe a
theorem here as a fact about JavaScript or IEEE-754 arithmetic.

Use the toolchain pinned in `lean-toolchain`. Verify changes with `lake build`, `lake test`, and `lake exe freerange` as applicable.

Keep the executable analyzer and its soundness proof aligned. Every new expression constructor needs concrete evaluation, abstract interpretation, reporting, focused positive and negative tests, and a corresponding case in the whole-expression soundness proof.

Do not commit `sorry`, `admit`, `axiom`, or `unsafe` proof shortcuts. Inspect the axioms of the public soundness theorems before release.

Prefer explicit finite data and structural recursion. Any widening, fixed-point iteration, path splitting, or relational domain must be specified before implementation because those choices can cause state growth and make proof obligations difficult to reverse.

Use atomic commits and preserve unrelated worktree changes.
