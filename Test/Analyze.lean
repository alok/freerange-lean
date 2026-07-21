import FreeRange.Analyze

open FreeRange

namespace FreeRangeTest.Analyze

def x : Var 1 := ⟨0⟩

def x2 : Var 2 := ⟨0⟩

def y2 : Var 2 := ⟨1⟩

def boundedPair : Context 2 := fun index =>
  if index = x2.index then .closed 1 10 else .closed 2 3

def boundedHundred : Context 1 := fun _ => .closed 0 100

def crossesZero : Context 1 := fun _ => .closed (-5) 5

def unconstrained : Context 1 := fun _ => .top

#guard analyze boundedPair (x2.expr + y2.expr) ==
  { number := .closed 3 13, requirements := [] }

#guard analyze boundedHundred (maxE 10 (minE x.expr 90)) ==
  { number := .closed 10 90, requirements := [] }

#guard analyze crossesZero (10 / x.expr) ==
  { number := .top, requirements := [.nonzero x.expr] }

#guard (analyze unconstrained (ifE (x ≠ᵍ 0) (10 / x.expr) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≠ᵍ 4) (10 / (x.expr - 4)) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≠ᵍ 5) (10 / (x.expr - 4)) 0)).requirements ==
  [.nonzero (x.expr - 4)]

#guard (analyze unconstrained (x.expr * x.expr)).number == .top

end FreeRangeTest.Analyze
