import FreeRange

open FreeRange

namespace FreeRangeDemo

def x : Var 1 := .at 0

def x2 : Var 2 := .at 0

def y2 : Var 2 := .at 1

def boundedPair : Context 2 := .ofVector #v[.closed 1 10, .closed 2 3]

def boundedHundred : Context 1 := .singleton (.closed 0 100)

def crossesZero : Context 1 := .singleton (.closed (-5) 5)

def unconstrained : Context 1 := .uniform .top

def addition : Expr 2 := x2 + y2

def multiplication : Expr 2 := x2 * y2

def clamp : Expr 1 := maxE 10 (minE x 90)

def quotient : Expr 1 := 10 / x

def guarded : Expr 1 := ifE (x ≠ᵍ 0) quotient 0

def shiftedGuard : Expr 1 := ifE (x ≠ᵍ 4) (10 / (x - 4)) 0

def wrongShift : Expr 1 := ifE (x ≠ᵍ 5) (10 / (x - 4)) 0

def divisorName : InputNames 1 := .singleton "divisor"

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
  let multiplicationOk ← expect "bounded multiplication" (report boundedPair multiplication)
    "range: [2, 30]\nrequires: none"
  let clampOk ← expect "clamp" (report boundedHundred clamp)
    "range: [10, 90]\nrequires: none"
  let quotientOk ← expect "unguarded division" (report crossesZero quotient)
    "range: [-∞, +∞]\nrequires: x0 != 0"
  let failedCheckOk ← expect "concrete x0 = 0"
    (checkAt crossesZero quotient (.singleton 0)).render
    "requirement failed: x0 != 0"
  let passingCheckOk ← expect "concrete x0 = 2"
    (checkAt crossesZero quotient (.singleton 2)).render
    "value: 5"
  let namedReportOk ← expect "named input" (reportWithNames crossesZero quotient divisorName)
    "range: [-∞, +∞]\nrequires: divisor != 0"
  let guardedOk ← expect "direct guard" (report unconstrained guarded)
    "range: [-∞, +∞]\nrequires: none"
  let shiftedOk ← expect "shifted guard" (report unconstrained shiftedGuard)
    "range: [-∞, +∞]\nrequires: none"
  let wrongShiftOk ← expect "wrong-shift negative control" (report unconstrained wrongShift)
    "range: [-∞, +∞]\nrequires: (x0 - 4) != 0"
  let allPassed := additionOk && multiplicationOk && clampOk && quotientOk && failedCheckOk &&
    passingCheckOk && namedReportOk && guardedOk && shiftedOk && wrongShiftOk
  if allPassed then
    IO.println "\nAll canonical checks passed."
    pure 0
  else
    pure 1

end FreeRangeDemo

def main : IO UInt32 := FreeRangeDemo.main
