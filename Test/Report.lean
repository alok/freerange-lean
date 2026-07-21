import FreeRange.Report

open FreeRange

namespace FreeRangeTest.Report

def x : Var 1 := ⟨0⟩

def x2 : Var 2 := ⟨0⟩

def y2 : Var 2 := ⟨1⟩

def boundedPair : Context 2 := fun index =>
  if index = x2.index then .closed 1 10 else .closed 2 3

def boundedHundred : Context 1 := fun _ => .closed 0 100

def crossesZero : Context 1 := fun _ => .closed (-5) 5

def unconstrained : Context 1 := fun _ => .top

#guard report boundedPair (x2.expr + y2.expr) == "range: [3, 13]\nrequires: none"

#guard report boundedHundred (maxE 10 (minE x.expr 90)) ==
  "range: [10, 90]\nrequires: none"

#guard report crossesZero (10 / x.expr) ==
  "range: [-∞, +∞]\nrequires: x0 != 0"

#guard (checkAt crossesZero (10 / x.expr) (fun _ => 0)).render ==
  "requirement failed: x0 != 0"

#guard checkAt crossesZero (10 / x.expr) (fun _ => 2) == .value 5

#guard checkAt crossesZero (10 / x.expr) (fun _ => 8) ==
  .inputOutsideContext 0 8 (.closed (-5) 5)

#guard report unconstrained (10 / (10 / x.expr)) ==
  "range: [-∞, +∞]\nrequires: x0 != 0\nrequires: (10 / x0) != 0"

#guard checkAt unconstrained (ifE (x =ᵍ 0) 1 (10 / x.expr)) (fun _ => 0) == .value 1

end FreeRangeTest.Report
