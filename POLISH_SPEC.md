# Release-grade polish specification

This document is the implementation contract for Linear issue `ALOK-800`. It extends the
initial `ALOK-796` contract in [`SPEC.md`](SPEC.md) without widening FreeRange's semantic
scope. The analyzer still interprets its own finite expression language over mathematical
integers. It does not analyze arbitrary Lean terms, JavaScript numbers, IEEE-754 values,
loops, mutable state, or recursive programs.

The target release is **FreeRange 0.2.0**. The version bump records observable precision
improvements and new public convenience APIs. Existing public theorem statements and the
default textual report format remain compatible.

## 1. Canonical abstract numbers

An exclusion is useful only when its point belongs to the accompanying interval. For
example, `[3, 5] except 0` denotes the same set as `[3, 5]`, so the former is not a canonical
representation.

`AbstractNumber.normalize` must:

- retain `excluded = some z` exactly when `z` is in the stored interval;
- drop an exclusion outside the interval;
- leave the interval unchanged; and
- preserve denotation exactly, witnessed by a public theorem
  `mem_normalize_iff`.

The library must also expose a proposition describing canonical abstract numbers and prove
that normalization produces one. Public abstract transformers must return normalized
results. Rendering must normalize its argument so that even a hand-constructed,
noncanonical value never prints a redundant `except` clause.

Normalization is representational only. It must not turn an interval with an excluded sole
point into a special empty-interval encoding, and it must not change the meaning of
`AbstractNumber.Mem`.

## 2. Multiplication precision

Constant multiplication remains exact through `scale`. When neither operand is a singleton,
the analyzer must additionally compute the standard four-corner interval hull whenever both
input intervals have finite lower and upper bounds:

```text
[a, b] * [c, d]
  = [min (a*c) (a*d) (b*c) (b*d),
     max (a*c) (a*d) (b*c) (b*d)]
```

The implementation may associate the four `min` and `max` operations internally in any
documented way. It must prove that every concrete product of members of the input intervals
belongs to that hull. If either input lacks a finite endpoint, the nonconstant fallback may
remain the top interval.

The result excludes zero when both operands prove that zero is absent. This fact must be
preserved for both the bounded-hull path and the top-interval fallback, and its soundness must
follow from integer multiplication's zero-product property. A single nonzero operand is not
enough to exclude zero from a product.

Required tests cover all four sign-stable quadrants, intervals that cross zero, the unbounded
fallback, constant multiplication, zero-exclusion propagation, and concrete membership in a
computed hull.

## 3. Construction ergonomics

Typical client code must not need `.expr` projections or repeated raw `Fin` functions.

The public API must provide:

- `Var.at` for constructing a variable from a `Fin n` index;
- heterogeneous `+`, `-`, `*`, and `/` expression operators for `Var`/`Var`,
  `Var`/`Expr`, and `Expr`/`Var` operands;
- `Context.uniform`, `Context.singleton`, and `Context.ofVector`;
- `Env.uniform`, `Env.singleton`, and `Env.ofVector`; and
- examples showing that guards, `ifE`, `minE`, `maxE`, and `absE` accept variables through
  the existing coercion to expressions.

The existing constructors and homogeneous `Expr` operators remain public. Convenience APIs
must elaborate to the same expression syntax and therefore require no new evaluator or
soundness cases.

## 4. Named reports

The default report remains byte-for-byte compatible and continues to call inputs `x0`, `x1`,
and so on.

Callers must also be able to supply a total naming function `Fin n -> String`. Named
rendering must cover every occurrence of an input inside:

- expressions;
- guards;
- division requirements;
- analysis reports; and
- point-check reports.

The naming layer is presentation-only. It must not alter an expression, context,
requirement, proof, or analysis result. Tests must compare exact default and custom-named
strings.

## 5. Executable documentation

The README quickstart must be mirrored by a dedicated Lean module included in the test
library. That module is the compilation check for the documented construction surface,
analysis call, soundness theorem, tactic, default report, named report, and point check.

Documentation must clearly distinguish:

- proved exact-integer soundness;
- abstract-interpretation precision choices;
- executable examples; and
- explicit non-goals.

Claims must stay within the theorem statements. In particular, no text may imply that the
library proves facts about arbitrary Lean programs or JavaScript/IEEE-754 execution.

## 6. Release hygiene

The 0.2.0 repository must include:

- a changelog with an honest 0.2.0 entry and the initial 0.1.0 release;
- contributing instructions with the pinned toolchain and verification commands;
- a `CITATION.cff` file containing only verified project metadata;
- current installation instructions for both a Lake dependency and a local clone; and
- package metadata whose version agrees with the changelog, citation file, Git tag, and
  GitHub release.

No generated dependency directory is committed. The package must still work as a fresh
downstream Lake dependency.

## 7. Proof and verification gates

The release is accepted only when all of the following hold:

1. `lake build --wfail` succeeds.
2. `lake test` succeeds.
3. `lake exe freerange` succeeds and its checked-in expectations match.
4. `lake env leanchecker` succeeds for the library root.
5. The public soundness theorem axiom audit lists only standard Lean principles already
   allowed by the initial specification.
6. Repository source contains no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration.
7. A clean external package can fetch the tagged dependency, compile the quickstart surface,
   and produce canonical reports.
8. GitHub Actions is green for the published commit.

The release notes and Linear issue must identify any deliberate precision boundary that
remains. Passing tests is not permission to claim a stronger theorem than the checked public
types provide.
