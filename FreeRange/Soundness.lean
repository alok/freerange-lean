import FreeRange.Analyze

namespace FreeRange

namespace AbstractNumber

theorem mem_refineTrue {abstract : AbstractNumber} {comparison : Comparison}
    {constant value : Int} (hmem : abstract.Mem value)
    (hguard : comparison.Holds value constant) :
    (abstract.refineTrue comparison constant).Mem value := by
  cases comparison with
  | eq =>
      subst value
      simp [refineTrue, exact, closed, Mem, Interval.closed, Interval.Mem,
        LowerBound.Holds, UpperBound.Holds]
  | ne =>
      refine ⟨hmem.1, ?_⟩
      simpa [refineTrue, exclude, Comparison.Holds, eq_comm] using hguard
  | lt =>
      apply mem_restrictUpper hmem
      simp [Comparison.Holds] at hguard
      omega
  | le => exact mem_restrictUpper hmem hguard
  | gt =>
      apply mem_restrictLower hmem
      simp [Comparison.Holds] at hguard
      omega
  | ge => exact mem_restrictLower hmem hguard

theorem mem_refineFalse {abstract : AbstractNumber} {comparison : Comparison}
    {constant value : Int} (hmem : abstract.Mem value)
    (hguard : ¬comparison.Holds value constant) :
    (abstract.refineFalse comparison constant).Mem value := by
  cases comparison with
  | eq =>
      refine ⟨hmem.1, ?_⟩
      simpa [refineFalse, exclude, Comparison.Holds, eq_comm] using hguard
  | ne =>
      have hequal : value = constant := by
        simp [Comparison.Holds] at hguard
        exact hguard
      subst value
      simp [refineFalse, exact, closed, Mem, Interval.closed, Interval.Mem,
        LowerBound.Holds, UpperBound.Holds]
  | lt =>
      apply mem_restrictLower hmem
      simp [Comparison.Holds] at hguard
      omega
  | le =>
      apply mem_restrictLower hmem
      simp [Comparison.Holds] at hguard
      omega
  | gt =>
      apply mem_restrictUpper hmem
      simp [Comparison.Holds] at hguard
      omega
  | ge =>
      apply mem_restrictUpper hmem
      simp [Comparison.Holds] at hguard
      omega

end AbstractNumber

namespace Context

theorem covers_set {context : Context inputCount} {environment : Env inputCount}
    {target : Fin inputCount} {number : AbstractNumber}
    (hcontext : context.Covers environment) (hnumber : number.Mem (environment target)) :
    (context.set target number).Covers environment := by
  intro index
  by_cases hequal : index = target
  · subst index
    simpa [set] using hnumber
  · simpa [set, hequal] using hcontext index

theorem covers_refineTrue {context : Context inputCount} {environment : Env inputCount}
    {guard : Guard inputCount} (hcontext : context.Covers environment)
    (hguard : guard.Holds environment) :
    (context.refineTrue guard).Covers environment := by
  apply covers_set hcontext
  exact AbstractNumber.mem_refineTrue (hcontext guard.input) hguard

theorem covers_refineFalse {context : Context inputCount} {environment : Env inputCount}
    {guard : Guard inputCount} (hcontext : context.Covers environment)
    (hguard : ¬guard.Holds environment) :
    (context.refineFalse guard).Covers environment := by
  apply covers_set hcontext
  exact AbstractNumber.mem_refineFalse (hcontext guard.input) hguard

end Context

/-- The analyzer over-approximates every successful result when its inferred requirements hold. -/
theorem analyze_sound (context : Context inputCount) (expression : Expr inputCount)
    (environment : Env inputCount) (hcontext : context.Covers environment)
    (hrequirements : Requirements.Hold (analyze context expression).requirements environment) :
    ∃ value, expression.eval environment = some value ∧
      (analyze context expression).number.Mem value := by
  induction expression generalizing context with
  | const constant =>
      refine ⟨constant, rfl, ?_⟩
      simp [analyze, AbstractNumber.exact, AbstractNumber.closed, AbstractNumber.Mem,
        Interval.closed, Interval.Mem, LowerBound.Holds, UpperBound.Holds]
  | input index =>
      exact ⟨environment index, rfl, hcontext index⟩
  | neg expression inductionHypothesis =>
      have hinner : Requirements.Hold (analyze context expression).requirements environment := by
        simpa [analyze] using hrequirements
      rcases inductionHypothesis context hcontext hinner with ⟨value, heval, hmem⟩
      refine ⟨-value, ?_, ?_⟩
      · simp [Expr.eval, heval]
      · simpa [analyze] using AbstractNumber.mem_neg hmem
  | add left right leftInduction rightInduction =>
      have hboth : Requirements.Hold
          ((analyze context left).requirements ++ (analyze context right).requirements)
          environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hleftRequirements, hrightRequirements⟩
      rcases leftInduction context hcontext hleftRequirements with ⟨leftValue, hleftEval, hleftMem⟩
      rcases rightInduction context hcontext hrightRequirements with ⟨rightValue, hrightEval, hrightMem⟩
      refine ⟨leftValue + rightValue, ?_, ?_⟩
      · simp [Expr.eval, hleftEval, hrightEval]
      · simpa [analyze] using AbstractNumber.mem_add hleftMem hrightMem
  | sub left right leftInduction rightInduction =>
      have hboth : Requirements.Hold
          ((analyze context left).requirements ++ (analyze context right).requirements)
          environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hleftRequirements, hrightRequirements⟩
      rcases leftInduction context hcontext hleftRequirements with ⟨leftValue, hleftEval, hleftMem⟩
      rcases rightInduction context hcontext hrightRequirements with ⟨rightValue, hrightEval, hrightMem⟩
      refine ⟨leftValue - rightValue, ?_, ?_⟩
      · simp [Expr.eval, hleftEval, hrightEval]
      · simpa [analyze] using AbstractNumber.mem_sub hleftMem hrightMem
  | mul left right leftInduction rightInduction =>
      have hboth : Requirements.Hold
          ((analyze context left).requirements ++ (analyze context right).requirements)
          environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hleftRequirements, hrightRequirements⟩
      rcases leftInduction context hcontext hleftRequirements with ⟨leftValue, hleftEval, hleftMem⟩
      rcases rightInduction context hcontext hrightRequirements with ⟨rightValue, hrightEval, hrightMem⟩
      refine ⟨leftValue * rightValue, ?_, ?_⟩
      · simp [Expr.eval, hleftEval, hrightEval]
      · simpa [analyze] using AbstractNumber.mem_mul hleftMem hrightMem
  | div dividend divisor dividendInduction divisorInduction =>
      by_cases hpoint : (analyze context divisor).number.pointExcluded 0 = true
      · have hprior : Requirements.Hold
            ((analyze context dividend).requirements ++ (analyze context divisor).requirements)
            environment := by
          simpa [analyze, hpoint] using hrequirements
        rcases Requirements.hold_append_iff.mp hprior with
          ⟨hdividendRequirements, hdivisorRequirements⟩
        rcases dividendInduction context hcontext hdividendRequirements with
          ⟨dividendValue, hdividendEval, hdividendMem⟩
        rcases divisorInduction context hcontext hdivisorRequirements with
          ⟨divisorValue, hdivisorEval, hdivisorMem⟩
        have hdivisorNonzero : divisorValue ≠ 0 := by
          intro hequal
          subst divisorValue
          exact AbstractNumber.not_mem_of_pointExcluded hpoint hdivisorMem
        refine ⟨dividendValue / divisorValue, ?_, ?_⟩
        · simp [Expr.eval, hdividendEval, hdivisorEval, hdivisorNonzero]
        · simp [analyze, hpoint]
      · have hall : Requirements.Hold
            (((analyze context dividend).requirements ++ (analyze context divisor).requirements) ++
              [.nonzero divisor]) environment := by
          simpa [analyze, hpoint] using hrequirements
        rcases Requirements.hold_append_iff.mp hall with ⟨hprior, hnew⟩
        rcases Requirements.hold_append_iff.mp hprior with
          ⟨hdividendRequirements, hdivisorRequirements⟩
        rcases dividendInduction context hcontext hdividendRequirements with
          ⟨dividendValue, hdividendEval, hdividendMem⟩
        rcases divisorInduction context hcontext hdivisorRequirements with
          ⟨divisorValue, hdivisorEval, hdivisorMem⟩
        have hrequirement : (Requirement.nonzero divisor).Holds environment :=
          hnew (.nonzero divisor) (by simp)
        rcases hrequirement with ⟨requiredValue, hrequiredEval, hrequiredNonzero⟩
        have hequal : divisorValue = requiredValue := by
          rw [hdivisorEval] at hrequiredEval
          exact Option.some.inj hrequiredEval
        have hdivisorNonzero : divisorValue ≠ 0 := by
          intro hzero
          apply hrequiredNonzero
          rw [← hequal]
          exact hzero
        refine ⟨dividendValue / divisorValue, ?_, ?_⟩
        · simp [Expr.eval, hdividendEval, hdivisorEval, hdivisorNonzero]
        · simp [analyze, hpoint]
  | minimum left right leftInduction rightInduction =>
      have hboth : Requirements.Hold
          ((analyze context left).requirements ++ (analyze context right).requirements)
          environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hleftRequirements, hrightRequirements⟩
      rcases leftInduction context hcontext hleftRequirements with ⟨leftValue, hleftEval, hleftMem⟩
      rcases rightInduction context hcontext hrightRequirements with ⟨rightValue, hrightEval, hrightMem⟩
      refine ⟨intMin leftValue rightValue, ?_, ?_⟩
      · simp [Expr.eval, hleftEval, hrightEval]
      · simpa [analyze] using AbstractNumber.mem_minimum hleftMem hrightMem
  | maximum left right leftInduction rightInduction =>
      have hboth : Requirements.Hold
          ((analyze context left).requirements ++ (analyze context right).requirements)
          environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hleftRequirements, hrightRequirements⟩
      rcases leftInduction context hcontext hleftRequirements with ⟨leftValue, hleftEval, hleftMem⟩
      rcases rightInduction context hcontext hrightRequirements with ⟨rightValue, hrightEval, hrightMem⟩
      refine ⟨intMax leftValue rightValue, ?_, ?_⟩
      · simp [Expr.eval, hleftEval, hrightEval]
      · simpa [analyze] using AbstractNumber.mem_maximum hleftMem hrightMem
  | absolute expression inductionHypothesis =>
      have hinner : Requirements.Hold (analyze context expression).requirements environment := by
        simpa [analyze] using hrequirements
      rcases inductionHypothesis context hcontext hinner with ⟨value, heval, hmem⟩
      refine ⟨Interval.intAbs value, ?_, ?_⟩
      · simp [Expr.eval, heval]
      · simpa [analyze] using AbstractNumber.mem_absolute hmem
  | ite guard thenBranch elseBranch thenInduction elseInduction =>
      have hboth : Requirements.Hold
          ((analyze (context.refineTrue guard) thenBranch).requirements ++
            (analyze (context.refineFalse guard) elseBranch).requirements) environment := by
        simpa [analyze] using hrequirements
      rcases Requirements.hold_append_iff.mp hboth with ⟨hthenRequirements, helseRequirements⟩
      by_cases hguard : guard.Holds environment
      · have hrefined : (context.refineTrue guard).Covers environment :=
          Context.covers_refineTrue hcontext hguard
        rcases thenInduction (context.refineTrue guard) hrefined hthenRequirements with
          ⟨value, heval, hmem⟩
        refine ⟨value, ?_, ?_⟩
        · simp [Expr.eval, hguard, heval]
        · simpa [analyze] using AbstractNumber.mem_join_left hmem
      · have hrefined : (context.refineFalse guard).Covers environment :=
          Context.covers_refineFalse hcontext hguard
        rcases elseInduction (context.refineFalse guard) hrefined helseRequirements with
          ⟨value, heval, hmem⟩
        refine ⟨value, ?_, ?_⟩
        · simp [Expr.eval, hguard, heval]
        · simpa [analyze] using AbstractNumber.mem_join_right hmem

/-- Requirement-free analysis proves total evaluation for every environment covered by the context. -/
theorem safe_of_no_requirements {context : Context inputCount} {expression : Expr inputCount}
    (hrequirements : (analyze context expression).requirements = []) :
    Safe context expression := by
  intro environment hcontext
  have hall : Requirements.Hold (analyze context expression).requirements environment := by
    intro requirement hmem
    rw [hrequirements] at hmem
    simp at hmem
  rcases analyze_sound context expression environment hcontext hall with ⟨value, heval, _⟩
  exact ⟨value, heval⟩

end FreeRange
