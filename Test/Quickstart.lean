import FreeRange

open FreeRange

namespace FreeRangeTest.Quickstart

def x : Var 1 := .at 0

def unconstrained : Context 1 := .uniform .top

def guardedDivision : Expr 1 :=
  ifE (x ≠ᵍ 0) (10 / x) 0

#guard report unconstrained guardedDivision ==
  "range: [-∞, +∞]\nrequires: none"

example : Safe unconstrained guardedDivision := by
  freerange

def shiftedDivision : Expr 1 :=
  ifE (x ≠ᵍ 4) (10 / (x - 4)) 0

example : Safe unconstrained shiftedDivision := by
  freerange

def x2 : Var 2 := .at 0

def y2 : Var 2 := .at 1

def boundedPair : Context 2 :=
  .ofVector #v[.closed 1 10, .closed 2 3]

def boundedAddition : Expr 2 := x2 + y2

#guard analyze boundedPair boundedAddition ==
  { number := .closed 3 13, requirements := [] }

#guard report boundedPair boundedAddition ==
  "range: [3, 13]\nrequires: none"

#guard report boundedPair (x2 * y2) ==
  "range: [2, 30]\nrequires: none"

theorem boundedAdditionSound (environment : Env 2)
    (hcontext : boundedPair.Covers environment) :
    ∃ value, boundedAddition.eval environment = some value ∧
      (analyze boundedPair boundedAddition).number.Mem value := by
  apply analyze_sound boundedPair boundedAddition environment hcontext
  intro requirement hrequirement
  simp [boundedAddition, x2, y2, Var.expr, Var.at, analyze] at hrequirement

def crossesZero : Context 1 := .singleton (.closed (-5) 5)

def divisorName : InputNames 1 := .singleton "divisor"

#guard reportWithNames crossesZero (10 / x) divisorName ==
  "range: [-∞, +∞]\nrequires: divisor != 0"

#guard (checkAt crossesZero (10 / x) (.singleton 0)).renderWithNames divisorName ==
  "requirement failed: divisor != 0"

#guard (checkAt crossesZero (10 / x) (.singleton 2)).renderWithNames divisorName ==
  "value: 5"

end FreeRangeTest.Quickstart
