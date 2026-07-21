# FreeRange Lean

[![CI](https://github.com/alok/freerange-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/alok/freerange-lean/actions/workflows/ci.yml)

FreeRange Lean is a pure Lean 4, proof-backed range analyzer for a small embedded
exact-integer language. Give it abstract ranges for the inputs and it computes:

- a range containing every successful result; and
- the nonzero conditions needed to make division safe.

The public `analyze_sound` theorem connects that computation to the language's
concrete semantics. The `freerange` tactic turns a requirement-free analysis into
a proof of safety; it is not a bounded test or counterexample search.

This project is inspired by Cheng Lou's
[FreeRange](https://github.com/chenglou/freerange), but it is a Lean library, not a
TypeScript port or bridge. Version 0.1 reasons about unbounded `Int`, not JavaScript
binary64 arithmetic. See [SEMANTICS.md](SEMANTICS.md) before applying a result to
floating-point code.

## A first proof

```lean
import FreeRange

open FreeRange

namespace Example

def x : Var 1 := ⟨0⟩

def unconstrained : Context 1 := fun _ => .top

def guardedDivision : Expr 1 :=
  ifE (x ≠ᵍ 0) (10 / x.expr) 0

#eval report unconstrained guardedDivision
-- range: [-∞, +∞]
-- requires: none

example : Safe unconstrained guardedDivision := by
  freerange

end Example
```

`Safe context expression` means that the expression evaluates successfully for
every concrete environment covered by `context`. The proof above works because
the true branch refines `x` to exclude zero before analyzing the divisor.

The refinement also follows an exclusion through an exact shift:

```lean
def shifted : Expr 1 :=
  ifE (x ≠ᵍ 4) (10 / (x.expr - 4)) 0

example : Safe unconstrained shifted := by
  freerange
```

Changing the guard to `x ≠ᵍ 5` correctly leaves the requirement
`(x0 - 4) != 0` unresolved.

## Reports and concrete checks

Contexts map each `Fin n` input index to an `AbstractNumber`:

```lean
def x2 : Var 2 := ⟨0⟩
def y2 : Var 2 := ⟨1⟩

def boundedPair : Context 2 := fun index =>
  if index = x2.index then .closed 1 10 else .closed 2 3

#eval report boundedPair (x2.expr + y2.expr)
-- range: [3, 13]
-- requires: none
```

An unguarded partial operation reports its caller contract:

```lean
def crossesZero : Context 1 := fun _ => .closed (-5) 5

#eval report crossesZero (10 / x.expr)
-- range: [-∞, +∞]
-- requires: x0 != 0
```

`checkAt` checks context membership first, then inferred requirements, then the
concrete evaluation:

```lean
#eval (checkAt crossesZero (10 / x.expr) (fun _ => 0)).render
-- requirement failed: x0 != 0

#eval (checkAt crossesZero (10 / x.expr) (fun _ => 2)).render
-- value: 5
```

This checker explains one supplied input. It is not the basis of the soundness
proof and it does not search for counterexamples.

## Embedded language

For `n` inputs, `Expr n` includes:

- integer constants and inputs indexed by `Fin n`;
- negation, addition, subtraction, multiplication, and partial integer division;
- `minE`, `maxE`, and `absE`;
- `ifE` with one input-to-constant guard.

`Var n` coerces to `Expr n`, and expressions support ordinary `-`, `+`, `-`, `*`,
and `/` notation. Guards use visibly distinct notation:

```lean
x =ᵍ 3
x ≠ᵍ 3
x <ᵍ 3
x ≤ᵍ 3
x >ᵍ 3
x ≥ᵍ 3
```

The range constructors are:

```lean
AbstractNumber.top
AbstractNumber.closed lower upper
AbstractNumber.atLeast lower
AbstractNumber.atMost upper
AbstractNumber.exact value
```

An abstract number is an inclusive interval, possibly unbounded on either side,
with at most one integer point excluded. Empty bounded intervals are allowed and
represent unreachable refinements.

## Proof authority

The central theorem is:

```lean
theorem analyze_sound
    (context : Context inputCount)
    (expression : Expr inputCount)
    (environment : Env inputCount)
    (hcontext : context.Covers environment)
    (hrequirements :
      Requirements.Hold (analyze context expression).requirements environment) :
    ∃ value,
      expression.eval environment = some value ∧
      (analyze context expression).number.Mem value
```

It proves two things together: evaluation succeeds under the inferred contract,
and the result belongs to the reported abstract range. Every abstract transformer
used by the analyzer has its corresponding membership theorem.

The corollary used by the tactic is:

```lean
theorem safe_of_no_requirements
    (hrequirements : (analyze context expression).requirements = []) :
    Safe context expression
```

The repository contains no `sorry`, `admit`, custom `axiom`, or `unsafe`
declaration. On Lean 4.32.0, `#print axioms` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` for both public theorems. CI also
runs an independent `.olean` declaration audit.

## Precision boundary

Sound does not mean maximally precise. Version 0.1 deliberately chooses a small,
auditable domain:

- addition, subtraction, negation, bounds, `min`, `max`, and absolute value use
  interval transformers;
- multiplication is interval-precise when either operand is an exact constant;
- multiplying two nonconstant abstract values returns `[-∞, +∞]`;
- division checks or infers nonzeroness, then returns `[-∞, +∞]`;
- branches are range-refined, while their inferred requirements are combined
  path-insensitively;
- only one excluded point is retained.

Those choices may produce a wide range or a stronger-than-necessary caller
contract, but `analyze_sound` still applies. The package does not silently turn a
precision failure into a false claim.

## Install

Add the Git dependency to a Lake package:

```lean
require freerange from git
  "https://github.com/alok/freerange-lean" @ "main"
```

Then import the umbrella module:

```lean
import FreeRange
```

The repository is pinned to `leanprover/lean4:v4.32.0` and has no third-party Lean
dependencies.

## Build and verify

```text
lake build
lake test
lake exe freerange
```

The executable is self-checking: it prints the canonical reports and exits with a
nonzero status if any report changes unexpectedly.

For the explicit theorem audit:

```text
printf 'import FreeRange\n#print axioms FreeRange.analyze_sound\n#print axioms FreeRange.safe_of_no_requirements\n' | lake env lean --stdin
```

## Repository map

| File | Role |
| --- | --- |
| `FreeRange/Range.lean` | Abstract bounds, intervals, exclusions, transformers, and local soundness proofs |
| `FreeRange/Expr.lean` | Embedded syntax, concrete `Option Int` semantics, contexts, and safety |
| `FreeRange/Analyze.lean` | Guard refinement, requirements, and executable abstract interpreter |
| `FreeRange/Soundness.lean` | Refinement proofs, whole-analyzer theorem, and safety corollary |
| `FreeRange/Report.lean` | Stable reports and concrete environment checking |
| `FreeRange/Tactic.lean` | The `freerange` proof tactic |
| `Test/` | Compile-time, executable, positive, and negative regression cases |
| `Main.lean` | Self-checking canonical demonstration |

For the complete contract, read [SPEC.md](SPEC.md). For the mathematical and
trust boundary, read [SEMANTICS.md](SEMANTICS.md). For the relationship to the
original project, read [UPSTREAM.md](UPSTREAM.md).

## Non-goals in version 0.1

FreeRange Lean does not currently parse arbitrary Lean declarations, model
floating point, analyze arrays or mutable state, summarize recursive functions,
or maintain relational facts between two unknown inputs. These are explicit
extension points, not implicit claims.

## License

FreeRange Lean is available under the MIT License. The upstream project is also
MIT licensed; attribution and the exact design-comparison revision are recorded
in [UPSTREAM.md](UPSTREAM.md).
