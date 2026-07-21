import FreeRange.Expr

open FreeRange

namespace FreeRangeTest.Expr

def x : Var 1 := ⟨0⟩

def five : Env 1 := fun _ => 5

def zero : Env 1 := fun _ => 0

#guard ((10 / x.expr : Expr 1).eval five) == some 2

#guard ((10 / x.expr : Expr 1).eval zero) == none

#guard ((ifE (x ≠ᵍ 0) (10 / x.expr) 0).eval five) == some 2

#guard ((ifE (x ≠ᵍ 0) (10 / x.expr) 0).eval zero) == some 0

#guard ((maxE 10 (minE x.expr 90)).eval five) == some 10

end FreeRangeTest.Expr
