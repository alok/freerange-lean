# Upstream relationship and attribution

FreeRange Lean is inspired by Cheng Lou's
[chenglou/freerange](https://github.com/chenglou/freerange), an MIT-licensed
TypeScript range analyzer.

The design comparison for version 0.1 was pinned to upstream commit
[`d48e5ee7dafb2e6939971adf0e37106958d95d24`](https://github.com/chenglou/freerange/tree/d48e5ee7dafb2e6939971adf0e37106958d95d24).
Pinning the revision makes the influence auditable even as either project changes.

Copyright in the upstream project remains with Cheng Lou. FreeRange Lean contains
an independent Lean implementation and does not vendor or execute the upstream
TypeScript sources. Both repositories use the MIT License.

## Design correspondence

The useful idea carried across is the product shape of a range analysis:

```text
program + input assumptions
            |
            v
     abstract analysis
       /           \
 result range   caller requirements
```

FreeRange Lean keeps the separation between inferred numeric information and
conditions required for safe execution. It also keeps conservative, branch-aware
analysis and human-readable reports.

The implementation and claim boundaries differ substantially:

| Concern | Upstream FreeRange | FreeRange Lean 0.2.0 |
| --- | --- | --- |
| Host and input | TypeScript tooling over a JavaScript-like program model | Pure Lean library over explicit `Expr n` values |
| Concrete numbers | JavaScript IEEE-754 binary64 behavior | Unbounded exact Lean `Int` |
| Numeric phenomena | Tracks float-specific states including non-finite behavior | No float, `NaN`, rounding, overflow, or underflow model |
| Program structure | Richer control flow, calls, loops, and contracts | Expressions plus input-to-constant conditional guards |
| Safety contract | Analyzer requirements in the upstream engine | `Requirement.nonzero expression` with a Lean definition |
| Assurance | Executable analyzer and upstream tests | Executable analyzer plus Lean membership and whole-analysis proofs |
| Integration | TypeScript/JavaScript ecosystem | Lake package, Lean API, and `freerange` tactic |

## Why the first Lean release is smaller

A direct feature-for-feature translation would require fixing and proving a large
floating-point and program-control semantics before any end-to-end soundness claim
could be made. Version 0.1 instead selects a coherent exact-integer core small
enough to prove completely:

- the abstract domain has a concrete membership relation;
- every supported transformer has a membership theorem;
- both sides of all six guards have refinement proofs;
- the entire analyzer has one compositional soundness theorem;
- requirement-free analyses turn into `Safe` proofs.

That is a semantic port of the central range-plus-requirements idea, not a claim of
source, feature, or floating-point compatibility.

## Future compatibility work

A future layer could approach upstream behavior by adding, in order:

1. a concrete binary64 semantics with explicit `NaN` and infinities;
2. proved float abstract transformers;
3. richer guards and relational refinements;
4. statements, control-flow joins, and loops;
5. function summaries and contracts;
6. a front end from elaborated Lean code to a proved expression model.

Each layer would need its own theorem connecting the new concrete semantics to
the reported abstract result. None of those extensions is implied by the current
exact-`Int` theorem.
