import FreeRange

open FreeRange

namespace FreeRangeDemo

def x : Var 1 := ⟨0⟩

def x2 : Var 2 := ⟨0⟩

def y2 : Var 2 := ⟨1⟩

def boundedPair : Context 2 := fun index =>
  if index = x2.index then .closed 1 10 else .closed 2 3

def boundedHundred : Context 1 := fun _ => .closed 0 100

def crossesZero : Context 1 := fun _ => .closed (-5) 5

def unconstrained : Context 1 := fun _ => .top

def addition : Expr 2 := x2.expr + y2.expr

def clamp : Expr 1 := maxE 10 (minE x.expr 90)

def quotient : Expr 1 := 10 / x.expr

def guarded : Expr 1 := ifE (x ≠ᵍ 0) quotient 0

def shiftedGuard : Expr 1 := ifE (x ≠ᵍ 4) (10 / (x.expr - 4)) 0

def wrongShift : Expr 1 := ifE (x ≠ᵍ 5) (10 / (x.expr - 4)) 0

def expect (label actual expected : String) : IO Bool := do
  IO.println s!"\n{label}\n{actual}"
  if actual = expected then
    pure true
  else
    IO.eprintln s!"expected:\n{expected}"
    pure false

def main : IO UInt32 := do
  IO.println "FreeRange Lean — proof-backed exact-Int range analysis"
  let additionOk ← expect "bounded addition" (report boundedPair addition)
    "range: [3, 13]\nrequires: none"
  let clampOk ← expect "clamp" (report boundedHundred clamp)
    "range: [10, 90]\nrequires: none"
  let quotientOk ← expect "unguarded division" (report crossesZero quotient)
    "range: [-∞, +∞]\nrequires: x0 != 0"
  let failedCheckOk ← expect "concrete x0 = 0"
    (checkAt crossesZero quotient (fun _ => 0)).render
    "requirement failed: x0 != 0"
  let passingCheckOk ← expect "concrete x0 = 2"
    (checkAt crossesZero quotient (fun _ => 2)).render
    "value: 5"
  let guardedOk ← expect "direct guard" (report unconstrained guarded)
    "range: [-∞, +∞]\nrequires: none"
  let shiftedOk ← expect "shifted guard" (report unconstrained shiftedGuard)
    "range: [-∞, +∞]\nrequires: none"
  let wrongShiftOk ← expect "wrong-shift negative control" (report unconstrained wrongShift)
    "range: [-∞, +∞]\nrequires: (x0 - 4) != 0"
  let allPassed := additionOk && clampOk && quotientOk && failedCheckOk && passingCheckOk &&
    guardedOk && shiftedOk && wrongShiftOk
  if allPassed then
    IO.println "\nAll canonical checks passed."
    pure 0
  else
    pure 1

end FreeRangeDemo

def main : IO UInt32 := FreeRangeDemo.main
