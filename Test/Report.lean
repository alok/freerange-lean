import FreeRange.Report

open FreeRange

namespace FreeRangeTest.Report

#guard ({ interval := Interval.closed 3 5, excluded := some 0 } : AbstractNumber).render ==
  "[3, 5]"

def x : Var 1 := .at 0

def x2 : Var 2 := .at 0

def y2 : Var 2 := .at 1

def boundedPair : Context 2 := .ofVector #v[.closed 1 10, .closed 2 3]

def boundedHundred : Context 1 := .singleton (.closed 0 100)

def crossesZero : Context 1 := .singleton (.closed (-5) 5)

def positiveDivisors : Context 1 := .singleton (.closed 2 5)

def unconstrained : Context 1 := .uniform .top

def unconstrainedPair : Context 2 := .uniform .top

def descriptiveNames : InputNames 2 := .ofVector #v["width", "height"]

#guard report boundedPair (x2 + y2) == "range: [3, 13]\nrequires: none"

#guard report boundedHundred (maxE 10 (minE x 90)) ==
  "range: [10, 90]\nrequires: none"

#guard report crossesZero (10 / x) ==
  "range: [-∞, +∞]\nrequires: x0 != 0"

#guard report positiveDivisors (10 / x) ==
  "range: [2, 5]\nrequires: none"

#guard reportWithNames positiveDivisors (10 / x) (.singleton "divisor") ==
  "range: [2, 5]\nrequires: none"

#guard checkAt positiveDivisors (10 / x) (.singleton 3) == .value 3

#guard (checkAt crossesZero (10 / x) (.singleton 0)).render ==
  "requirement failed: x0 != 0"

#guard checkAt crossesZero (10 / x) (.singleton 2) == .value 5

#guard checkAt crossesZero (10 / x) (.singleton 8) ==
  .inputOutsideContext 0 8 (.closed (-5) 5)

#guard report unconstrained (10 / (10 / x)) ==
  "range: [-∞, +∞]\nrequires: x0 != 0\nrequires: (10 / x0) != 0"

#guard checkAt unconstrained (ifE (x =ᵍ 0) 1 (10 / x)) (.singleton 0) == .value 1

#guard report unconstrained (ifE (x >ᵍ 0) (10 / x) 0) ==
  "range: [0, 10]\nrequires: none"

#guard (x2 >ᵍ 0).renderWithNames descriptiveNames == "width > 0"

#guard ((ifE (x2 >ᵍ 0) (x2 + y2) (x2 - y2) : Expr 2).renderWithNames descriptiveNames) ==
  "if width > 0 then (width + height) else (width - height)"

#guard reportWithNames unconstrainedPair (10 / (x2 + y2)) descriptiveNames ==
  "range: [-∞, +∞]\nrequires: (width + height) != 0"

#guard reportWithNames unconstrainedPair (10 / (x2 + y2)) defaultInputName ==
  report unconstrainedPair (10 / (x2 + y2))

#guard (checkAt unconstrainedPair (10 / y2) (Env.ofVector #v[3, 0])).renderWithNames
    descriptiveNames == "requirement failed: height != 0"

#guard (checkAt boundedPair (x2 + y2) (Env.ofVector #v[0, 2])).renderWithNames
    descriptiveNames == "input width = 0 is outside [1, 10]"

end FreeRangeTest.Report
