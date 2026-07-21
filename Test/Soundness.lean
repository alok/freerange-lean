import FreeRange.Tactic

open FreeRange

namespace FreeRangeTest.Soundness

def x : Var 1 := .at 0

def unconstrained : Context 1 := .uniform .top

def guarded : Expr 1 := ifE (x ≠ᵍ 0) (10 / x) 0

def shiftedGuard : Expr 1 := ifE (x ≠ᵍ 4) (10 / (x - 4)) 0

def equalityFalseBranch : Expr 1 := ifE (x =ᵍ 0) 1 (10 / x)

def positiveTrueBranch : Expr 1 := ifE (x >ᵍ 0) (10 / x) 0

def positiveFalseBranch : Expr 1 := ifE (x <ᵍ 1) 0 (10 / x)

example : Safe unconstrained guarded := by
  freerange

example : Safe unconstrained shiftedGuard := by
  freerange

example : Safe unconstrained equalityFalseBranch := by
  freerange

example : Safe unconstrained positiveTrueBranch := by
  freerange

example : Safe unconstrained positiveFalseBranch := by
  freerange

example : (Requirement.nonzero x).check (.singleton 2) = true := by
  decide

example : (Requirement.nonzero x).check (.singleton 0) = false := by
  decide

end FreeRangeTest.Soundness
