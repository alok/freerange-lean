# Semantics, soundness, and trust boundary

This document fixes the meaning of a FreeRange Lean 0.3.0 result. It is normative
for claims made by this repository.

## What is being analyzed

FreeRange Lean analyzes values of the inductive type `Expr n`. It does not inspect
arbitrary Lean syntax, elaborated declarations, compiler IR, or machine code.
Users construct the embedded expression explicitly and separately state an
abstract range for each of its `n` inputs.

The concrete environment type is:

```lean
Env n = Fin n → Int
```

The abstract input context type is:

```lean
Context n = Fin n → AbstractNumber
```

A context covers an environment exactly when every concrete input is a member of
the corresponding abstract number.

## Concrete expression semantics

`Expr.eval environment expression : Option Int` is the reference semantics.

- Constants and inputs evaluate directly.
- Negation, addition, subtraction, multiplication, `min`, `max`, and absolute
  value use Lean's exact unbounded integer operations.
- Division uses Lean's Euclidean `Int` division operation when the divisor is nonzero.
- Division by zero evaluates to `none`.
- Evaluation is strict: a failed subexpression makes its enclosing expression
  fail.
- A conditional evaluates only the branch selected by its guard.

For a positive divisor, Lean `Int` division rounds toward negative infinity. Negative
divisors satisfy `a / (-b) = -(a / b)`. This is not rational division or truncation toward
zero.

Division by zero is the only concrete failure in version 0.3.0. The semantics has no
overflow, underflow, rounding, `NaN`, or numeric infinity. The infinity symbols in
a report are abstract unbounded endpoints, not concrete values.

## Guards

A `Guard n` compares one `Fin n` input directly with an `Int` constant. The six
relations are equality, disequality, strict and non-strict less-than, and strict
and non-strict greater-than.

For an integer constant `c`, branch refinement is:

| Guard | True branch | False branch |
| --- | --- | --- |
| `x = c` | `x` is exactly `c` | exclude `c` |
| `x != c` | exclude `c` | `x` is exactly `c` |
| `x < c` | upper bound `c - 1` | lower bound `c` |
| `x <= c` | upper bound `c` | lower bound `c + 1` |
| `x > c` | lower bound `c + 1` | upper bound `c` |
| `x >= c` | lower bound `c` | upper bound `c - 1` |

The `±1` steps are exact because the domain is `Int`. Refinement intersects new
bounds with existing bounds. Setting a new excluded point may forget an older
excluded point because the domain stores only one; forgetting information widens
the abstraction and remains sound.

`mem_refineTrue` and `mem_refineFalse` prove that any covered concrete input which
takes the corresponding branch remains in the refined abstract input.

## Abstract numbers

An `AbstractNumber` contains:

1. a lower endpoint, either a finite integer or negative infinity;
2. an upper endpoint, either a finite integer or positive infinity; and
3. an optional excluded integer.

For concrete integer `z`, membership means both interval bounds hold and the
optional exclusion is not `z`. A finite interval with lower endpoint greater than
its upper endpoint is empty. A singleton interval that excludes its singleton is
also empty. Empty values are useful for branches that are unreachable under the
input context.

`AbstractNumber.normalize` drops a stored exclusion exactly when that point lies
outside the interval. For example, `[1, 4] except 0` canonicalizes to `[1, 4]`,
while `[-1, 1] except 0` retains its useful nonzero evidence.
`mem_normalize_iff` proves that this transformation preserves concrete membership
in both directions, and `normalize_isNormalized` proves that the resulting
exclusion—if any—belongs to the interval.

All public abstract transformers produce canonical results. Rendering normalizes
its argument as a final presentation boundary, including when a caller manually
constructs a noncanonical structure. Normalization does not introduce a separate
empty representation: a singleton interval excluding its sole point remains the
existing empty abstract value.

## Abstract transformers

Each transformer is an over-approximation. If its operands contain concrete
values, the result contains the corresponding concrete operation.

### Join

Join takes the interval hull. It preserves zero as excluded whenever both inputs
prove zero absent, including when that absence follows from bounds rather than a
stored exclusion. Otherwise, it retains an excluded point only when both operands
store the same point.

Consequently, joining `[-5, -1]` with `[1, 5]` yields `[-5, 5] except 0`, and a
later division can use the retained nonzero fact.

### Negation, addition, and subtraction

Negation reverses interval endpoints and negates a stored exclusion.

Addition and subtraction compute the ordinary interval image. When one operand is
an exact constant, the implementation also retains the particular excluded-point
fact needed to prove that the result is not zero. For example, excluding `4` from
`x` lets `x - 4` exclude zero. Other translated exclusions may be forgotten.

### Multiplication

If either operand denotes an exact singleton, multiplication scales the other
interval by that constant. Positive and negative coefficients order the endpoints
appropriately. A nonzero coefficient carries a proof that zero remains absent
when the source proves zero absent.

When neither operand is exact and both intervals have finite endpoints, multiplication
uses the standard four-corner hull:

```text
[a, b] * [c, d]
  = [min (a*c) (a*d) (b*c) (b*d),
     max (a*c) (a*d) (b*c) (b*d)]
```

`Interval.mem_productHull` proves containment for every concrete pair in the input
intervals. The proof covers all sign configurations, including intervals that cross
zero.

If either nonconstant interval is unbounded, multiplication returns the top interval.
That deliberate precision fallback retains zero as excluded exactly when both operands
prove zero absent. Soundness follows from the integer zero-product theorem; one nonzero
operand alone cannot justify excluding zero.

### Minimum, maximum, and absolute value

Minimum and maximum use the endpoint-wise interval images. Absolute value handles
negative, positive, crossing-zero, and unbounded intervals separately. These
operations currently discard excluded-point precision where it is not needed for
soundness.

### Division

The analyzer first analyzes both operands. If the abstract divisor already proves
that zero is absent, it adds no new requirement. Otherwise it appends
`nonzero divisor`.

Range precision is computed independently from that safety decision:

- An exact nonzero singleton divisor maps every available dividend endpoint. Positive
  divisors preserve endpoint order, negative divisors reverse it, and unbounded dividend
  endpoints remain unbounded in the corresponding output direction.
- A finite dividend and finite wholly positive divisor interval use the minimum and maximum
  of the four endpoint quotients. A wholly negative divisor interval reduces to its negated
  positive interval and negates the quotient hull.
- A finite dividend and one-sided wholly positive divisor ray use the hull of the two finite
  endpoint quotients and zero. A negative divisor ray again reduces by negation. Including
  zero is deliberately conservative and can be wider than the smallest valid integer hull.
- Every remaining case returns the top interval. In particular, a zero-straddling divisor
  interval remains top even if the abstract number's separate excluded point removes zero.

`Interval.mem_edivConst`, `Interval.mem_quotientHull_of_pos`,
`Interval.mem_quotientRayHull_of_pos`, and `Interval.mem_ediv` establish the local interval
claims. `AbstractNumber.mem_ediv` lifts them through normalization, and `analyze_sound` uses
that theorem after separately proving the concrete divisor nonzero.

An excluded dividend point is transported only for an exact divisor `1` or `-1`; the latter
negates the point. Division by any larger absolute value is not injective, so other
exclusions are forgotten. The resulting interval bounds can still prove zero absent and
discharge a later division requirement compositionally.

These cases are sound over-approximations. Version 0.3.0 does not claim that every returned
quotient interval is minimal.

## Requirements

The first requirement form is:

```lean
Requirement.nonzero expression
```

It holds in a concrete environment only when `expression` both evaluates
successfully and produces a nonzero integer. This conjunctive definition matters
for nested division: the analyzer returns requirements for the inner expression
before the outer nonzero condition.

Requirements from sequential subexpressions are appended in evaluation order.
Requirements from both conditional branches are also appended. That branch policy
is deliberately path-insensitive: callers may receive requirements from a branch
their particular input does not take, and even from an abstractly unreachable
branch. The contract can therefore be stronger than necessary, never weaker than
the theorem needs.

Requirements are not deduplicated or simplified in version 0.3.0.

## Whole-analyzer theorem

`analyze_sound` states:

> If the abstract context covers a concrete environment, and every inferred
> requirement holds in that environment, then concrete evaluation returns a value
> and that value is a member of the reported abstract number.

The proof is structural induction on `Expr`. It composes separately proved
membership lemmas for each abstract transformer and proved preservation lemmas for
both sides of every guard.

This is both a safety and range theorem. A report with a requirement is a
conditional theorem, not an assertion that the expression is unconditionally
safe.

`safe_of_no_requirements` specializes the theorem: if computation shows the
returned requirement list is empty, every covered environment evaluates
successfully. The `freerange` tactic applies that corollary and uses Lean's kernel
decision procedure to discharge the closed equality saying that the computed list
is empty. It does not sample inputs or introduce `native_decide`'s generated axiom.

## Proof and execution trust

The soundness source contains no `sorry`, `admit`, custom `axiom`, or `unsafe`
declaration. With the pinned Lean 4.32.0 toolchain, the audit is:

```text
'FreeRange.analyze_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FreeRange.safe_of_no_requirements' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical/quotient axioms, not project-specific assumptions.
The compile-time audit also checks that a representative theorem produced by the
`freerange` tactic has exactly the same set. CI builds and tests the package, runs
the self-checking executable, rejects source placeholders, and runs Lean 4.32's
bundled standalone `leanchecker` over the built environment.

As with ordinary Lean development, the final trust base includes Lean's kernel and
the correctness of the concrete definitions being claimed as the intended model.
The core `analyze_sound` theorem is available directly when a user wants to supply
requirements rather than use the requirement-free tactic.

## JavaScript and floating-point boundary

The original TypeScript FreeRange analyzes JavaScript-style numeric programs and
tracks phenomena such as non-finite values and integrality. FreeRange Lean 0.3.0
does none of that.

In particular, a FreeRange Lean proof about `Expr n` does not establish that a
syntactically similar JavaScript, Lean `Float`, C `double`, or hardware computation
has the same range. Translating such a result requires a proved refinement from
that target's floating-point semantics to this exact-integer model, or a new
analyzer whose transformers are proved against the target semantics.

## Scope of a report

Given:

```text
range: [3, 13]
requires: none
```

the justified claim is:

> For every exact-integer environment covered by the supplied context, evaluating
> the supplied embedded expression succeeds and returns an integer between 3 and
> 13 inclusive.

It is not a claim about arbitrary source code, machine integers, floating point,
execution cost, absence of non-arithmetic exceptions, or completeness of the
reported interval.
