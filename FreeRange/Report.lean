import FreeRange.Soundness

namespace FreeRange

namespace LowerBound

/-- Render a lower endpoint for a human-readable report. -/
def render : LowerBound → String
  | .negInf => "-∞"
  | .finite value => toString value

end LowerBound

namespace UpperBound

/-- Render an upper endpoint for a human-readable report. -/
def render : UpperBound → String
  | .finite value => toString value
  | .posInf => "+∞"

end UpperBound

namespace Interval

/-- Render an interval with inclusive endpoints. -/
def render (interval : Interval) : String :=
  s!"[{interval.lower.render}, {interval.upper.render}]"

end Interval

namespace AbstractNumber

/-- Render an abstract number, including its one excluded point when present. -/
def render (number : AbstractNumber) : String :=
  match number.excluded with
  | none => number.interval.render
  | some excluded => s!"{number.interval.render} except {excluded}"

end AbstractNumber

namespace Comparison

/-- Render a guard comparison. -/
def render : Comparison → String
  | .eq => "="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

end Comparison

namespace Guard

/-- Render an input-to-constant guard. -/
def render (guard : Guard inputCount) : String :=
  s!"x{guard.input.val} {guard.comparison.render} {guard.constant}"

end Guard

namespace Expr

/-- Render an embedded expression with explicit binary parentheses. -/
def render : Expr inputCount → String
  | .const value => toString value
  | .input index => s!"x{index.val}"
  | .neg value => s!"(-{value.render})"
  | .add left right => s!"({left.render} + {right.render})"
  | .sub left right => s!"({left.render} - {right.render})"
  | .mul left right => s!"({left.render} * {right.render})"
  | .div dividend divisor => s!"({dividend.render} / {divisor.render})"
  | .minimum left right => s!"min({left.render}, {right.render})"
  | .maximum left right => s!"max({left.render}, {right.render})"
  | .absolute value => s!"abs({value.render})"
  | .ite guard thenBranch elseBranch =>
      s!"if {guard.render} then {thenBranch.render} else {elseBranch.render}"

end Expr

namespace Requirement

/-- Render an inferred caller requirement. -/
def render : Requirement inputCount → String
  | .nonzero expression => s!"{expression.render} != 0"

end Requirement

namespace Analysis

/-- Render a deterministic two-part range-and-requirements report. -/
def render (analysis : Analysis inputCount) : String :=
  let requirements :=
    match analysis.requirements with
    | [] => "requires: none"
    | requirements =>
        String.intercalate "\n" (requirements.map fun (requirement : Requirement inputCount) =>
          s!"requires: {requirement.render}")
  s!"range: {analysis.number.render}\n{requirements}"

end Analysis

/-- Analyze and render one expression. -/
def report (context : Context inputCount) (expression : Expr inputCount) : String :=
  (analyze context expression).render

/-- The result of checking one concrete environment against an analysis. -/
inductive CheckResult (inputCount : Nat) where
  | inputOutsideContext (index : Fin inputCount) (value : Int) (expected : AbstractNumber)
  | requirementFailed (requirement : Requirement inputCount)
  | value (value : Int)
  | evaluationFailed
  deriving Repr, DecidableEq, BEq

namespace CheckResult

/-- Render a concrete check result. -/
def render : CheckResult inputCount → String
  | .inputOutsideContext index actualValue expected =>
      s!"input x{index.val} = {actualValue} is outside {expected.render}"
  | .requirementFailed requirement => s!"requirement failed: {requirement.render}"
  | .value resultValue => s!"value: {resultValue}"
  | .evaluationFailed => "evaluation failed after all inferred requirements passed"

end CheckResult

private def firstUncovered? (context : Context inputCount) (environment : Env inputCount) :
    Option (Fin inputCount) :=
  (List.finRange inputCount).find? fun index =>
    decide (¬(context index).Mem (environment index))

private def firstFailedRequirement? (requirements : List (Requirement inputCount))
    (environment : Env inputCount) : Option (Requirement inputCount) :=
  requirements.find? fun requirement => !requirement.check environment

/-- Check context membership, inferred requirements, and evaluation at one concrete environment. -/
def checkAt (context : Context inputCount) (expression : Expr inputCount)
    (environment : Env inputCount) : CheckResult inputCount :=
  match firstUncovered? context environment with
  | some index => .inputOutsideContext index (environment index) (context index)
  | none =>
      let analysis := analyze context expression
      match firstFailedRequirement? analysis.requirements environment with
      | some requirement => .requirementFailed requirement
      | none =>
          match expression.eval environment with
          | some value => .value value
          | none => .evaluationFailed

end FreeRange
