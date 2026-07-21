# Changelog

All notable changes to FreeRange Lean are recorded here. The project follows
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - 2026-07-21

### Added

- `Interval.edivConst` and its membership theorem for exact nonzero divisors over finite,
  one-sided, and fully unbounded dividends.
- Proved four-corner quotient hulls for finite wholly positive and wholly negative divisor
  intervals.
- Proved zero-inclusive quotient hulls for finite dividends over one-sided sign-stable
  divisor rays.
- `AbstractNumber.ediv`, with sound exclusion transport for the injective divisors `1` and
  `-1` only.
- A normative division specification plus transformer, analyzer, composition, report,
  executable, and compiled-quickstart regressions.

### Changed

- Division analysis now reports proved quotient bounds for supported sign-stable ranges
  instead of always returning the top interval after establishing safety.
- Guard-refined positive and negative divisor rays compose with quotient analysis; for
  example, `if x > 0 then 10 / x else 0` reports `[0, 10]` with no requirements.
- A quotient whose bounds prove zero absent can discharge a later division requirement.
- Documentation now states Lean's Euclidean `Int` division semantics and separates safety
  requirements from range precision.

### Precision boundaries

- A divisor interval that straddles zero still yields the top quotient interval, even when
  its separate excluded point removes zero.
- Unsupported unbounded non-singleton combinations retain the top fallback.
- Ray hulls conservatively include zero and are not claimed to be minimal.

### Compatibility

- The embedded language, concrete evaluator, requirement inference order, and public
  soundness theorem statements are unchanged.
- Existing 0.2.0 programs remain source-compatible. Reports for sign-stable division may be
  strictly narrower, which is the intended observable minor-release improvement.

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
- Lake restores complete cached artifacts so standalone declaration checkers work after a
  clean build.

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

[0.3.0]: https://github.com/alok/freerange-lean/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/alok/freerange-lean/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/alok/freerange-lean/releases/tag/v0.1.0
