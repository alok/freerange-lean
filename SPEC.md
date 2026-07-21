# FreeRange Lean v0.1 specification

## Objective

Build a pure Lean 4 range analyzer inspired by [chenglou/freerange](https://github.com/chenglou/freerange), pinned for design comparison at upstream commit `d48e5ee7dafb2e6939971adf0e37106958d95d24`. The package analyzes a small embedded numeric language, infers output ranges and safety requirements, and proves that its abstract interpretation is sound for the supported semantics.

The package is for Lean programs. It does not parse TypeScript, call the TypeScript compiler API, or invoke an external solver. “Ergo” in the original request means that the public Lean API should be ergonomic.

## Semantic boundary

FreeRange Lean v0.1 uses unbounded exact `Int` values. This is intentionally different from upstream FreeRange, whose concrete semantics are JavaScript IEEE-754 binary64 numbers and therefore include rounding, overflow, underflow, `NaN`, and infinities.

The exact-integer choice gives the first Lean package a small concrete semantics that can be proved without trusting a floating-point model. Reports and documentation must never imply that an integer proof establishes an IEEE-754 fact. A future float layer may reuse the expression, requirement, report, and tactic interfaces only after it supplies its own concrete semantics and sound abstract transformers.

## Supported embedded language

For `n` inputs, `Expr n` supports:

- integer constants and variables indexed by `Fin n`;
- negation, addition, subtraction, multiplication, and partial integer division;
- `min`, `max`, and absolute value;
- conditional expressions guarded by one input-to-constant comparison.

`Guard n` supports `=`, `≠`, `<`, `≤`, `>`, and `≥`. Restricting guards to an input and an integer constant makes branch refinement explicit, predictable, and provable. The expression operators should use ordinary Lean notation where that remains unambiguous. The public `Var n` wrapper and guard notations such as `x ≠ᵍ 0` should keep examples readable.

Division is the only partial operation in v0.1. `Expr.eval` returns `none` when a divisor evaluates to zero. Every other supported operation is total under exact-integer semantics.

## Abstract domain

`AbstractNumber` consists of:

- a lower bound that is either negative infinity or a finite integer;
- an upper bound that is either a finite integer or positive infinity;
- at most one excluded integer point.

Membership means that the concrete integer satisfies both bounds and is not the excluded point. Empty bounded intervals are representable and are useful for unreachable branch refinements.

The analyzer must implement sound transformers for constants, joins, negation, addition, subtraction, multiplication, `min`, `max`, and absolute value. Multiplication should be precise when either operand is a known constant; multiplying two nonconstant ranges may conservatively return the full range in v0.1. Division may conservatively return the full range after establishing a nonzero divisor.

An input-to-constant inequality narrows the corresponding bound. A disequality records the excluded point. Exact integer addition/subtraction by a constant and multiplication by a nonzero constant forward a relevant exclusion to zero. This must make the common guard `x ≠ 4` discharge the divisor requirement for `x - 4`.

Branch joins keep an excluded point only when both branches exclude it. Zero receives special consideration so that joining a negative range and a positive range can retain the fact that zero is impossible.

## Requirements and analysis

`analyze context expression` returns:

- an `AbstractNumber` covering every successful result;
- a list of inferred requirements.

The first requirement form is `nonzero expression`. The analyzer adds it when a divisor’s inferred value may contain zero. If the abstract divisor excludes zero, no requirement is added. Requirements from both conditional branches are path-insensitive and are returned together, matching upstream FreeRange’s conservative contract style.

A requirement holds in an environment when its expression evaluates successfully to a nonzero integer. The whole-expression theorem may assume every returned requirement. A requirement-free analysis therefore proves that evaluation cannot fail for any environment covered by the input context.

## Proof obligations

The repository must prove, without `sorry` or custom axioms:

1. Each abstract transformer contains the corresponding concrete operation result whenever its operands contain the concrete inputs.
2. Guard refinement preserves every concrete environment that takes the corresponding branch.
3. `analyze_sound`: if a context covers an environment and every inferred requirement holds, evaluation succeeds and the returned abstract number contains the result.
4. `safe_of_no_requirements`: if analysis returns no requirements, the expression is safe for every covered environment.

Proofs may use Lean’s standard logical axioms introduced by ordinary library definitions, but the final audit must print the axioms of the two public soundness theorems and document the result.

## Ergonomic surface

The public package must provide:

- readable constructors for closed, lower-bounded, upper-bounded, and unconstrained input ranges;
- `Var n`, coercion to `Expr n`, arithmetic notation, guard notation, and `ifE`;
- a deterministic text report containing the inferred range and requirements;
- a concrete checker that identifies the first failed requirement for a supplied environment;
- a `freerange` tactic that proves goals of the form `Safe context expression` when computation shows that the inferred requirement list is empty;
- a small executable that prints the canonical examples and exits successfully only if their expected analyses hold.

The tactic must reduce to the proved soundness theorem plus a decidable computation. It must not prove safety by bounded testing.

## Acceptance examples

The test suite must cover each requirement through both its producing and consuming path.

### Bounded addition

With `x ∈ [1, 10]` and `y ∈ [2, 3]`, analyzing `x + y` must report exactly:

```text
range: [3, 13]
requires: none
```

The whole-expression soundness theorem is the authority for every concrete pair in those ranges; example enumeration is only a regression test.

### Clamp

With `x ∈ [0, 100]`, analyzing `max 10 (min x 90)` must report exactly:

```text
range: [10, 90]
requires: none
```

This composes two abstract transformers rather than testing either transformer in isolation.

### Unguarded division

With `x ∈ [-5, 5]`, analyzing `10 / x` must report exactly:

```text
range: [-∞, +∞]
requires: x0 != 0
```

Checking the expression at `x = 0` must return exactly:

```text
requirement failed: x0 != 0
```

Checking it at `x = 2` must return the value `5`.

### Direct guard

With unconstrained `x`, analyzing `if x ≠ 0 then 10 / x else 0` must report no requirements. `by freerange` must prove its `Safe` goal.

### Shifted guard

With unconstrained `x`, analyzing `if x ≠ 4 then 10 / (x - 4) else 0` must report no requirements. This is the positive control for excluded-point propagation through subtraction. The nearby negative control `if x ≠ 5 then 10 / (x - 4) else 0` must still report `(x0 - 4) != 0`.

### Join

Joining `[-5, -1]` and `[1, 5]` must produce `[-5, 5]` excluding zero. A subsequent division by that joined abstract value must not invent a nonzero requirement.

### Unsupported precision

With two unconstrained, nonconstant inputs, analyzing `x * y` may report `[-∞, +∞]`, but it must remain sound and must not claim a narrower range. This is a deliberate precision limit, not unsupported syntax.

## Repository artifacts

The public repository must contain:

- Lean library modules split into domain, syntax/semantics, analysis, soundness, reporting, and tactic layers;
- compile-time and executable tests;
- `README.md`, `SEMANTICS.md`, upstream attribution, MIT license, and API examples;
- GitHub Actions running the same build and test commands used locally;
- a clean git history with atomic commits;
- a link from Linear project `FreeRange Lean` and issue `ALOK-796` to the published GitHub repository.

## Verification gates

Completion requires all of the following on the published commit:

```text
lake build
lake test
lake exe freerange
```

The audit must also establish that there are no `sorry` declarations, no custom axioms, no unexpected working-tree changes, and that the GitHub default branch points at the locally verified commit.

## Deliberate non-goals for v0.1

- parsing or analyzing arbitrary Lean declarations automatically;
- TypeScript parsing or compatibility;
- IEEE-754, `Float`, `NaN`, infinity, overflow, underflow, or rounding claims;
- arrays, records, mutable module state, loops, recursion, or cross-function summaries;
- relational domains involving two unknown inputs;
- automatic counterexample search beyond checking a supplied concrete environment;
- pretending that an unconstrained result range is a precise numeric guarantee.

These boundaries keep the first release useful, executable, and fully checkable. Later features must extend both concrete semantics and the matching soundness theorem.
