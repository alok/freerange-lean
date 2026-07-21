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

def splitAroundZero : Context 1 := fun _ =>
  AbstractNumber.join (.closed (-5) (-1)) (.closed 1 5)

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

#guard analyze splitAroundZero (10 / x.expr) ==
  { number := .top, requirements := [] }

#guard (analyze unconstrained (10 / (10 / x.expr))).requirements ==
  [.nonzero x.expr, .nonzero (10 / x.expr)]

#guard (analyze unconstrained (ifE (x =ᵍ 0) 1 (10 / x.expr))).requirements == []

#guard (analyze unconstrained (ifE (x <ᵍ 0) (10 / x.expr) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≤ᵍ (-1)) (10 / x.expr) 0)).requirements == []

#guard (analyze unconstrained (ifE (x >ᵍ 0) (10 / x.expr) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≥ᵍ 1) (10 / x.expr) 0)).requirements == []

#guard (analyze unconstrained (ifE (x <ᵍ 1) 0 (10 / x.expr))).requirements == []

#guard (analyze unconstrained (ifE (x ≤ᵍ 0) 0 (10 / x.expr))).requirements == []

#guard (analyze unconstrained (ifE (x >ᵍ (-1)) 0 (10 / x.expr))).requirements == []

#guard (analyze unconstrained (ifE (x ≥ᵍ 0) 0 (10 / x.expr))).requirements == []

#guard (analyze unconstrained (ifE (x =ᵍ 0) (10 / (0 : Expr 1)) 1)).requirements ==
  [.nonzero 0]

#guard (analyze unconstrained (x.expr * x.expr)).number == .top

#guard (analyze boundedHundred (x.expr * x.expr)).number == .closed 0 10000

end FreeRangeTest.Analyze
