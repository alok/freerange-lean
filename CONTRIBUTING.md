# Contributing

Thanks for helping improve FreeRange Lean. Changes are welcome when they preserve the
project's explicit theorem boundary: the library analyzes its own finite expression language
over exact Lean integers, not arbitrary Lean source or IEEE-754 execution.

## Set up the repository

Clone the repository with Git, enter it, and let Lean's toolchain manager select the version
in `lean-toolchain`. FreeRange has no third-party Lean dependencies.

Before editing behavior, read:

- [`SPEC.md`](SPEC.md) for the original semantic contract;
- [`POLISH_SPEC.md`](POLISH_SPEC.md) for the 0.2.0 additions; and
- [`SEMANTICS.md`](SEMANTICS.md) for the precise claim and trust boundary.

## Verify a change

Run the same gates as CI:

```text
lake build --wfail
lake test
lake exe freerange
lake lint FreeRange --lint-only=linter.all
lake env leanchecker
lake build +Test.Axioms --wfail
```

The final two commands independently check compiled declarations and guard the documented
axiom boundary. Also confirm that Lean source contains no `sorry`, `admit`, custom `axiom`,
or `unsafe` declaration.

## Keep semantics and proofs aligned

Every new expression constructor needs all of the following in the same change:

1. concrete evaluation in `Expr.eval`;
2. abstract interpretation in `analyze`;
3. human-readable rendering;
4. focused positive and negative tests; and
5. a corresponding case in `analyze_sound`.

Every precision improvement to an abstract transformer needs a membership theorem before it
can be used by the analyzer. Preserve the statements of the public soundness theorems unless
a release specification explicitly calls for a contract change.

## Documentation and release discipline

- Keep examples concise and compile important public snippets in `Test/Quickstart.lean`.
- Separate proved guarantees from executable observations and precision heuristics.
- Update `CHANGELOG.md` for user-visible changes.
- Keep `lakefile.lean`, `CITATION.cff`, release tags, and release notes on the same version.
- Make small, atomic commits with intent-revealing messages.

Please use [GitHub Issues](https://github.com/alok/freerange-lean/issues) for bugs and focused
feature proposals. Larger semantic additions should describe their concrete model, abstract
domain, proof obligations, and expected state-growth behavior before implementation.
