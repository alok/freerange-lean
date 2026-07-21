# Semantics, soundness, and trust boundary

This document fixes the meaning of a FreeRange Lean 0.1 result. It is normative
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
- Division uses Lean's `Int` division operation when the divisor is nonzero.
- Division by zero evaluates to `none`.
- Evaluation is strict: a failed subexpression makes its enclosing expression
  fail.
- A conditional evaluates only the branch selected by its guard.

Division by zero is the only concrete failure in version 0.1. The semantics has no
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

The representation is intentionally not normalized. For example, `[1, 4] except
0` is semantically the same set as `[1, 4]`. This keeps useful nonzero evidence
available to later operations without complicating the trusted membership
definition.

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

If neither operand is exact, version 0.1 returns the top abstract number. This is a
precision limit; it is still a sound over-approximation.

### Minimum, maximum, and absolute value

Minimum and maximum use the endpoint-wise interval images. Absolute value handles
negative, positive, crossing-zero, and unbounded intervals separately. These
operations currently discard excluded-point precision where it is not needed for
soundness.

### Division

The analyzer first analyzes both operands. If the abstract divisor already proves
that zero is absent, it adds no new requirement. Otherwise it appends
`nonzero divisor`.

After establishing this safety condition, version 0.1 returns the top abstract
number for the quotient. It makes no quotient-bound claim.

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

Requirements are not deduplicated or simplified in version 0.1.

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
successfully. The `freerange` tactic applies that corollary and uses
`native_decide` only to discharge the closed, decidable equality saying that the
computed list is empty. It does not sample inputs.

## Proof and execution trust

The soundness source contains no `sorry`, `admit`, custom `axiom`, or `unsafe`
declaration. With the pinned Lean 4.32.0 toolchain, the audit is:

```text
'FreeRange.analyze_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FreeRange.safe_of_no_requirements' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard logical/quotient axioms, not project-specific assumptions.
CI builds and tests the package, runs the self-checking executable, rejects source
placeholders, and asks `lean-action`'s independent declaration checker to inspect
the produced `.olean` files.

As with ordinary Lean development, the final trust base includes Lean's kernel and
the correctness of the concrete definitions being claimed as the intended model.
Using the `freerange` tactic additionally uses Lean's native decision procedure to
produce the closed computational premise. The core `analyze_sound` theorem is
available directly when a user wants to supply requirements without that tactic.

## JavaScript and floating-point boundary

The original TypeScript FreeRange analyzes JavaScript-style numeric programs and
tracks phenomena such as non-finite values and integrality. FreeRange Lean 0.1
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
