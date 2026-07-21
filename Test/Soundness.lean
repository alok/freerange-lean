import FreeRange.Tactic

open FreeRange

namespace FreeRangeTest.Soundness

def x : Var 1 := ⟨0⟩

def unconstrained : Context 1 := fun _ => .top

def guarded : Expr 1 := ifE (x ≠ᵍ 0) (10 / x.expr) 0

def shiftedGuard : Expr 1 := ifE (x ≠ᵍ 4) (10 / (x.expr - 4)) 0

example : Safe unconstrained guarded := by
  freerange

example : Safe unconstrained shiftedGuard := by
  freerange

example : (Requirement.nonzero x.expr).check (fun _ => 2) = true := by
  native_decide

example : (Requirement.nonzero x.expr).check (fun _ => 0) = false := by
  native_decide

end FreeRangeTest.Soundness
