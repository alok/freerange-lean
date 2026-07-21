# Changelog

All notable changes to FreeRange Lean are recorded here. The project follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2026-07-21

### Added

- A proved four-corner multiplication hull for any two finite bounded intervals.
- `AbstractNumber.normalize`, exact membership preservation via `mem_normalize_iff`, and a
  public canonical-form predicate.
- `Var.at`, mixed `Var`/`Expr` arithmetic, and sized-vector, singleton, and uniform helpers
  for contexts and environments.
- Caller-provided input names throughout expressions, guards, requirements, reports, and
  concrete check results.
- A compiled quickstart module, contribution guide, and software citation metadata.

### Changed

- Abstract transformers and rendering now discard exclusions that lie outside their interval.
- Nonconstant bounded multiplication reports useful bounds instead of the top interval.
- Multiplication preserves a zero exclusion when both operands prove zero absent, including
  on the deliberately unbounded fallback path.
- Examples and the self-checking executable use the concise public construction API.

### Compatibility

- The embedded language and exact-`Int` theorem boundary are unchanged.
- Existing constructors, `.expr`, and default `x0` report names remain available.
- Existing public soundness theorem statements and default report strings are unchanged.

## [0.1.0] - 2026-07-21

- Initial pure Lean 4 exact-integer expression language and abstract range domain.
- Proved local transformers, guard refinement, `analyze_sound`, and
  `safe_of_no_requirements`.
- Division requirements, deterministic reports, concrete point checks, the `freerange`
  tactic, executable examples, CI, axiom guards, and standalone environment checking.

[0.2.0]: https://github.com/alok/freerange-lean/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/alok/freerange-lean/releases/tag/v0.1.0
