import FreeRange.Soundness

namespace FreeRange

/-- A total presentation name for every embedded input. -/
abbrev InputNames (inputCount : Nat) := Fin inputCount → String

/-- The stable default input name used by existing reports. -/
def defaultInputName (index : Fin inputCount) : String := s!"x{index.val}"

namespace InputNames

/-- A name map for a one-input expression. -/
def singleton (name : String) : InputNames 1 := fun _ => name

/-- Build a total input-name map from an exactly sized vector. -/
def ofVector (names : Vector String inputCount) : InputNames inputCount := names.get

end InputNames

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

/-- Render an abstract number canonically, including its useful excluded point when present. -/
def render (number : AbstractNumber) : String :=
  let number := number.normalize
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

/-- Render a guard with caller-provided input names. -/
def renderWithNames (guard : Guard inputCount) (inputNames : InputNames inputCount) : String :=
  s!"{inputNames guard.input} {guard.comparison.render} {guard.constant}"

/-- Render an input-to-constant guard. -/
def render (guard : Guard inputCount) : String :=
  guard.renderWithNames defaultInputName

end Guard

namespace Expr

/-- Render an embedded expression with caller-provided input names. -/
def renderWithNames : (expression : Expr inputCount) → InputNames inputCount → String
  | .const value, _ => toString value
  | .input index, inputNames => inputNames index
  | .neg value, inputNames => s!"(-{value.renderWithNames inputNames})"
  | .add left right, inputNames =>
      s!"({left.renderWithNames inputNames} + {right.renderWithNames inputNames})"
  | .sub left right, inputNames =>
      s!"({left.renderWithNames inputNames} - {right.renderWithNames inputNames})"
  | .mul left right, inputNames =>
      s!"({left.renderWithNames inputNames} * {right.renderWithNames inputNames})"
  | .div dividend divisor, inputNames =>
      s!"({dividend.renderWithNames inputNames} / {divisor.renderWithNames inputNames})"
  | .minimum left right, inputNames =>
      s!"min({left.renderWithNames inputNames}, {right.renderWithNames inputNames})"
  | .maximum left right, inputNames =>
      s!"max({left.renderWithNames inputNames}, {right.renderWithNames inputNames})"
  | .absolute value, inputNames => s!"abs({value.renderWithNames inputNames})"
  | .ite guard thenBranch elseBranch, inputNames =>
      s!"if {guard.renderWithNames inputNames} then {thenBranch.renderWithNames inputNames} else {elseBranch.renderWithNames inputNames}"

/-- Render an embedded expression with explicit binary parentheses. -/
def render (expression : Expr inputCount) : String :=
  expression.renderWithNames defaultInputName

end Expr

namespace Requirement

/-- Render an inferred caller requirement with caller-provided input names. -/
def renderWithNames (requirement : Requirement inputCount)
    (inputNames : InputNames inputCount) : String :=
  match requirement with
  | .nonzero expression => s!"{expression.renderWithNames inputNames} != 0"

/-- Render an inferred caller requirement. -/
def render (requirement : Requirement inputCount) : String :=
  requirement.renderWithNames defaultInputName

end Requirement

namespace Analysis

/-- Render a deterministic report with caller-provided input names. -/
def renderWithNames (analysis : Analysis inputCount)
    (inputNames : InputNames inputCount) : String :=
  let requirements :=
    match analysis.requirements with
    | [] => "requires: none"
    | requirements =>
        String.intercalate "\n" (requirements.map fun (requirement : Requirement inputCount) =>
          s!"requires: {requirement.renderWithNames inputNames}")
  s!"range: {analysis.number.render}\n{requirements}"

/-- Render a deterministic two-part range-and-requirements report. -/
def render (analysis : Analysis inputCount) : String :=
  analysis.renderWithNames defaultInputName

end Analysis

/-- Analyze and render one expression. -/
def report (context : Context inputCount) (expression : Expr inputCount) : String :=
  (analyze context expression).render

/-- Analyze and render one expression with caller-provided input names. -/
def reportWithNames (context : Context inputCount) (expression : Expr inputCount)
    (inputNames : InputNames inputCount) : String :=
  (analyze context expression).renderWithNames inputNames

/-- The result of checking one concrete environment against an analysis. -/
inductive CheckResult (inputCount : Nat) where
  /-- One concrete input is not covered by its abstract context entry. -/
  | inputOutsideContext (index : Fin inputCount) (value : Int) (expected : AbstractNumber)
  /-- The first inferred caller requirement that does not hold. -/
  | requirementFailed (requirement : Requirement inputCount)
  /-- Successful concrete evaluation. -/
  | value (value : Int)
  /-- Evaluation failed despite all inferred requirements passing. -/
  | evaluationFailed
  deriving Repr, DecidableEq, BEq

namespace CheckResult

/-- Render a concrete check result with caller-provided input names. -/
def renderWithNames (result : CheckResult inputCount)
    (inputNames : InputNames inputCount) : String :=
  match result with
  | .inputOutsideContext index actualValue expected =>
      s!"input {inputNames index} = {actualValue} is outside {expected.render}"
  | .requirementFailed requirement =>
      s!"requirement failed: {requirement.renderWithNames inputNames}"
  | .value resultValue => s!"value: {resultValue}"
  | .evaluationFailed => "evaluation failed after all inferred requirements passed"

/-- Render a concrete check result. -/
def render (result : CheckResult inputCount) : String :=
  result.renderWithNames defaultInputName

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
