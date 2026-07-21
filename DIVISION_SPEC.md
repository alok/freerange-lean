# Sign-stable division specification

This document is the implementation contract for Linear issue `ALOK-802`. It extends
[`SPEC.md`](SPEC.md) and [`POLISH_SPEC.md`](POLISH_SPEC.md) for the target FreeRange Lean
**0.3.0** release. When this document is silent, the earlier contracts remain in force.

The milestone improves the abstract range reported for division. It does not widen the
concrete language or its trust boundary: FreeRange still analyzes explicitly constructed
`Expr n` values over Lean's exact, unbounded `Int` type. It does not inspect arbitrary Lean
terms and does not model JavaScript, IEEE-754, fixed-width overflow, or machine arithmetic.

## 1. Concrete division remains unchanged

`Expr.eval` remains the reference semantics. It evaluates both operands, rejects a zero
divisor with `none`, and otherwise returns Lean's exact integer quotient:

```lean
if divisorValue = 0 then none else some (dividendValue / divisorValue)
```

The `/` operation here is Lean `Int` Euclidean division, not rational division and not
truncation toward zero. In particular, division by a positive integer rounds toward negative
infinity, while division by a negative integer is fixed by Lean's law
`a / (-b) = -(a / b)`.

The existing safety contract is unchanged. A divisor that might be zero still produces a
`Requirement.nonzero`; a divisor whose abstract value proves zero absent does not. Better
quotient ranges must not weaken, remove, or reinterpret caller requirements.

## 2. Quotient interval cases

The new interval transformer must be total and conservative. For concrete members `x` and
`y`, it must contain Lean's integer quotient `x / y`. The whole-analyzer proof separately
establishes `y != 0` before using the quotient as a successful `Expr.eval` result.

The transformer supports the following precision cases, in order.

### 2.1 Exact nonzero divisor

If the divisor interval is the singleton `[d, d]` with `d != 0`, divide every available
dividend endpoint by `d`.

- For `d > 0`, endpoint order is preserved.
- For `d < 0`, endpoint order is reversed.
- A missing lower or upper dividend endpoint remains unbounded in the corresponding output
  direction.

This case applies to finite, one-sided, and fully unbounded dividends. Examples include:

```text
[1, +infinity] / [2, 2]     = [0, +infinity]
[1, +infinity] / [-2, -2]   = [-infinity, 0]
[-infinity, -1] / [2, 2]    = [-infinity, -1]
```

An exact zero divisor does not use this case. Its interval result may be top because the
successful-evaluation theorem can only be applied under an unsatisfiable nonzero
requirement.

### 2.2 Finite sign-stable divisor

For finite dividend `[a, b]` and finite divisor `[c, d]`, use a four-corner quotient hull
when the divisor interval has one strict sign:

```text
0 < c
```

or

```text
d < 0
```

For a positive divisor interval, the hull is:

```text
[min (a/c) (a/d) (b/c) (b/d),
 max (a/c) (a/d) (b/c) (b/d)]
```

For a negative divisor interval, the implementation may compute the same four corners
directly or reduce to the positive interval `[-d, -c]` using `x / y = -(x / (-y))` and
negate the resulting hull.

The theorem must cover every sign pattern of the dividend, including an interval that
crosses zero. It must use Lean integer-division laws rather than a rational-arithmetic
argument that silently assumes exact quotients.

### 2.3 One-sided sign-stable divisor ray

For finite dividend `[a, b]` and positive divisor ray `[c, +infinity]` with `0 < c`, use the
conservative hull of the two finite endpoint quotients and zero:

```text
[min (a/c) (b/c) 0, max (a/c) (b/c) 0]
```

Zero is a safe abstract limiting endpoint. It intentionally sacrifices the possible tighter
upper bound `-1` for an everywhere-negative dividend under a positive divisor ray; version
0.3.0 does not claim a minimal hull.

For a negative divisor ray `[-infinity, d]` with `d < 0`, reduce to the positive ray
`[-d, +infinity]` and negate its hull.

This case is required so a guard such as `x > 0` can turn `10 / x` into a bounded result in
the selected branch instead of retaining the old top range.

### 2.4 Conservative fallbacks

Return the top interval for all remaining combinations, including:

- a divisor interval that contains or straddles zero;
- a zero-straddling interval whose separate excluded point happens to remove zero;
- a non-singleton divisor with an unsupported unbounded shape; and
- an unbounded dividend with a non-singleton divisor.

These are precision boundaries, not unsupported syntax. Requirement inference still proves
or requests nonzeroness independently. In particular, `[-5, 5] except 0` is safe as a
divisor but retains a top quotient interval because the nonrelational interval component
crosses zero.

Empty intervals may flow through any branch. The membership theorem is authoritative; when
an operand denotes no concrete members, its premise is uninhabited.

## 3. Abstract-number exclusions

The quotient interval is lifted to `AbstractNumber` and normalized like every other public
transformer.

An excluded dividend point may be transported only when the abstract divisor is proved to
be the exact value `1` or `-1`:

- division by `1` retains the excluded point;
- division by `-1` negates the excluded point; and
- every other case forgets the exclusion.

This boundary is required because integer division by a divisor with absolute value greater
than one is not injective. Removing one dividend cannot generally prove that its quotient is
absent. The transformer must not infer a zero exclusion merely because the dividend excludes
zero: for example, `1 / 2 = 0`.

Normalization may remove a transported exclusion if it lies outside the quotient interval.
The public membership theorem must prove that every quotient of operand members belongs to
the normalized result.

## 4. Analyzer integration

The `.div` case of `analyze` must compute the new abstract quotient from the already analyzed
dividend and divisor numbers. It must preserve the exact existing order and contents of
requirements:

1. dividend requirements;
2. divisor requirements; and
3. a new `nonzero divisor` requirement exactly when the divisor abstract number does not
   prove zero absent.

No requirement deduplication, path splitting, or relational state is introduced in this
milestone. Nested division may therefore continue to produce multiple requirements.

`analyze_sound` must use the new quotient membership theorem in both division branches: the
branch where the abstract divisor already excludes zero and the branch where a supplied
requirement establishes it. The concrete evaluator proof remains responsible for showing
the divisor is nonzero.

Downstream analysis must benefit compositionally. If a quotient interval itself excludes
zero through its bounds, a later division may consume that fact without adding a new
requirement.

## 5. Required regressions

Tests must exercise computation and proof surfaces, not only rendered examples.

### Interval and abstract-number tests

- all four sign combinations for finite dividend and divisor intervals;
- a dividend interval crossing zero;
- positive and negative one-sided divisor rays;
- positive and negative exact singleton divisors with one-sided dividends;
- exact `1` and `-1` exclusion transport;
- non-injective divisors forgetting exclusions;
- a divisor range that straddles zero returning top;
- a zero-straddling range excluding zero still returning top; and
- concrete membership examples for finite hull, ray hull, and exact-divisor paths.

### Analyzer and composition tests

- `10 / x` for finite positive and finite negative input ranges;
- `10 / x` under positive and negative guards that create divisor rays;
- `x / 2` and `x / -2` for one-sided dividend contexts;
- unchanged unguarded zero-crossing requirement behavior;
- unchanged safe-but-top fallback for a zero-excluded crossing interval;
- a bounded quotient used as the divisor of a second division; and
- a negative control where the first quotient can include zero and the second division still
  requires nonzeroness.

### Reporting, execution, and theorem tests

- exact default and custom-named report strings for at least one precise quotient;
- successful and failed concrete point checks remain unchanged;
- direct use of the quotient membership theorem;
- representative `Safe` goals closed by `freerange`; and
- the public axiom audit remains exactly the accepted standard Lean boundary.

## 6. Documentation and release contract

The README and semantics guide must describe division precision by case and explicitly state
that the hull is conservative rather than always optimal. At least one compiled quickstart or
executable example must visibly demonstrate a precise sign-stable quotient range.

Release metadata must agree on version `0.3.0`: Lake package metadata, changelog,
`CITATION.cff`, installation snippet, Git tag, and GitHub release. The 0.2.0 tag remains the
published compatibility baseline.

Completion requires:

```text
lake build --wfail
lake test
lake exe freerange
lake lint FreeRange --lint-only=linter.all
lake env leanchecker
lake build +Test.Axioms --wfail
```

The source audit must find no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration. A
fresh downstream package must be able to fetch the release revision, compile the public API,
and observe the documented quotient report. GitHub Actions must be green on the released
commit.

## 7. Deliberate non-goals

Version 0.3.0 does not add:

- arbitrary Lean-source or compiler-IR analysis;
- rational, real, JavaScript, or floating-point semantics;
- fixed-width overflow or division-overflow behavior;
- relational facts between dividend and divisor;
- disjoint interval unions for a zero-excluded crossing divisor;
- path-sensitive requirement collection;
- a guarantee of the narrowest representable quotient interval; or
- new concrete failure modes.

Any later extension of those boundaries needs its own explicit semantics and corresponding
soundness proof.
