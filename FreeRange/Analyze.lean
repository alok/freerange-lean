import FreeRange.Expr

namespace FreeRange

namespace AbstractNumber

/-- Refine one abstract input on the true branch of an input-to-constant guard. -/
def refineTrue (abstract : AbstractNumber) (comparison : Comparison) (constant : Int) :
    AbstractNumber :=
  match comparison with
  | .eq => exact constant
  | .ne => abstract.exclude constant
  | .lt => abstract.restrictUpper (constant - 1)
  | .le => abstract.restrictUpper constant
  | .gt => abstract.restrictLower (constant + 1)
  | .ge => abstract.restrictLower constant

/-- Refine one abstract input on the false branch of an input-to-constant guard. -/
def refineFalse (abstract : AbstractNumber) (comparison : Comparison) (constant : Int) :
    AbstractNumber :=
  match comparison with
  | .eq => abstract.exclude constant
  | .ne => exact constant
  | .lt => abstract.restrictLower constant
  | .le => abstract.restrictLower (constant + 1)
  | .gt => abstract.restrictUpper constant
  | .ge => abstract.restrictUpper (constant - 1)

end AbstractNumber

namespace Context

/-- Replace one input's abstract value. -/
def set (context : Context inputCount) (target : Fin inputCount) (value : AbstractNumber) :
    Context inputCount :=
  fun index => if index = target then value else context index

/-- Refine the guarded input for the true branch. -/
def refineTrue (context : Context inputCount) (guard : Guard inputCount) : Context inputCount :=
  context.set guard.input ((context guard.input).refineTrue guard.comparison guard.constant)

/-- Refine the guarded input for the false branch. -/
def refineFalse (context : Context inputCount) (guard : Guard inputCount) : Context inputCount :=
  context.set guard.input ((context guard.input).refineFalse guard.comparison guard.constant)

end Context

/-- A condition that callers must satisfy for an expression to evaluate safely. -/
inductive Requirement (inputCount : Nat) where
  /-- The expression must evaluate successfully to a nonzero integer. -/
  | nonzero (expression : Expr inputCount)
  deriving Repr, DecidableEq, BEq

namespace Requirement

/-- Semantic validity of one inferred requirement in a concrete environment. -/
def Holds (requirement : Requirement inputCount) (environment : Env inputCount) : Prop :=
  match requirement with
  | .nonzero expression =>
      ∃ value, expression.eval environment = some value ∧ value ≠ 0

/-- Executably check one inferred requirement in a concrete environment. -/
def check (requirement : Requirement inputCount) (environment : Env inputCount) : Bool :=
  match requirement with
  | .nonzero expression =>
      match expression.eval environment with
      | some value => decide (value ≠ 0)
      | none => false

theorem check_eq_true_iff {requirement : Requirement inputCount} {environment : Env inputCount} :
    requirement.check environment = true ↔ requirement.Holds environment := by
  cases requirement with
  | nonzero expression =>
      simp only [check, Holds]
      cases heval : expression.eval environment with
      | none => simp
      | some value => simp

end Requirement

namespace Requirements

/-- Every inferred requirement holds in a concrete environment. -/
def Hold (requirements : List (Requirement inputCount)) (environment : Env inputCount) : Prop :=
  ∀ requirement, requirement ∈ requirements → requirement.Holds environment

theorem hold_append_iff {left right : List (Requirement inputCount)} {environment : Env inputCount} :
    Hold (left ++ right) environment ↔ Hold left environment ∧ Hold right environment := by
  constructor
  · intro h
    exact ⟨fun requirement hmem => h requirement (List.mem_append_left right hmem),
      fun requirement hmem => h requirement (List.mem_append_right left hmem)⟩
  · rintro ⟨hleft, hright⟩ requirement hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hleft requirement hmem
    · exact hright requirement hmem

end Requirements

/-- The inferred result range and caller requirements for one expression. -/
structure Analysis (inputCount : Nat) where
  /-- An abstract number containing every result covered by the theorem. -/
  number : AbstractNumber
  /-- Caller obligations sufficient for successful evaluation. -/
  requirements : List (Requirement inputCount)
  deriving Repr, DecidableEq, BEq

/-- Analyze an embedded expression by forward abstract interpretation. -/
def analyze (context : Context inputCount) : Expr inputCount → Analysis inputCount
  | .const value => ⟨.exact value, []⟩
  | .input index => ⟨context index, []⟩
  | .neg value =>
      let result := analyze context value
      ⟨result.number.neg, result.requirements⟩
  | .add left right =>
      let leftResult := analyze context left
      let rightResult := analyze context right
      ⟨leftResult.number.add rightResult.number,
        leftResult.requirements ++ rightResult.requirements⟩
  | .sub left right =>
      let leftResult := analyze context left
      let rightResult := analyze context right
      ⟨leftResult.number.sub rightResult.number,
        leftResult.requirements ++ rightResult.requirements⟩
  | .mul left right =>
      let leftResult := analyze context left
      let rightResult := analyze context right
      ⟨leftResult.number.mul rightResult.number,
        leftResult.requirements ++ rightResult.requirements⟩
  | .div dividend divisor =>
      let dividendResult := analyze context dividend
      let divisorResult := analyze context divisor
      let priorRequirements := dividendResult.requirements ++ divisorResult.requirements
      let requirements :=
        if divisorResult.number.pointExcluded 0 = true then priorRequirements
        else priorRequirements ++ [.nonzero divisor]
      ⟨.top, requirements⟩
  | .minimum left right =>
      let leftResult := analyze context left
      let rightResult := analyze context right
      ⟨leftResult.number.minimum rightResult.number,
        leftResult.requirements ++ rightResult.requirements⟩
  | .maximum left right =>
      let leftResult := analyze context left
      let rightResult := analyze context right
      ⟨leftResult.number.maximum rightResult.number,
        leftResult.requirements ++ rightResult.requirements⟩
  | .absolute value =>
      let result := analyze context value
      ⟨result.number.absolute, result.requirements⟩
  | .ite guard thenBranch elseBranch =>
      let thenResult := analyze (context.refineTrue guard) thenBranch
      let elseResult := analyze (context.refineFalse guard) elseBranch
      ⟨thenResult.number.join elseResult.number,
        thenResult.requirements ++ elseResult.requirements⟩

end FreeRange
