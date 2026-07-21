import FreeRange.Analyze

open FreeRange

namespace FreeRangeTest.Analyze

def x : Var 1 := .at 0

def x2 : Var 2 := .at 0

def y2 : Var 2 := .at 1

def boundedPair : Context 2 := .ofVector #v[.closed 1 10, .closed 2 3]

def boundedHundred : Context 1 := .singleton (.closed 0 100)

def crossesZero : Context 1 := .singleton (.closed (-5) 5)

def positiveDivisors : Context 1 := .singleton (.closed 2 5)

def negativeDivisors : Context 1 := .singleton (.closed (-5) (-2))

def positiveRay : Context 1 := .singleton (.atLeast 1)

def negativeRay : Context 1 := .singleton (.atMost (-1))

def nonnegative : Context 1 := .singleton (.atLeast 0)

def unconstrained : Context 1 := .uniform .top

def splitAroundZero : Context 1 :=
  .singleton (AbstractNumber.join (.closed (-5) (-1)) (.closed 1 5))

#guard analyze boundedPair (x2 + y2) ==
  { number := .closed 3 13, requirements := [] }

#guard analyze boundedHundred (maxE 10 (minE x 90)) ==
  { number := .closed 10 90, requirements := [] }

#guard analyze crossesZero (10 / x) ==
  { number := .top, requirements := [.nonzero x] }

#guard analyze positiveDivisors (10 / x) ==
  { number := .closed 2 5, requirements := [] }

#guard analyze negativeDivisors (10 / x) ==
  { number := .closed (-5) (-2), requirements := [] }

#guard analyze positiveRay (10 / x) ==
  { number := .closed 0 10, requirements := [] }

#guard analyze negativeRay (10 / x) ==
  { number := .closed (-10) 0, requirements := [] }

#guard analyze nonnegative (x / 2) ==
  { number := .atLeast 0, requirements := [] }

#guard analyze positiveRay (x / (-2)) ==
  { number := .atMost 0, requirements := [] }

#guard (analyze unconstrained (ifE (x ≠ᵍ 0) (10 / x) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≠ᵍ 4) (10 / (x - 4)) 0)).requirements == []

#guard (analyze unconstrained (ifE (x ≠ᵍ 5) (10 / (x - 4)) 0)).requirements ==
  [.nonzero (x - 4)]

#guard analyze splitAroundZero (10 / x) ==
  { number := .top, requirements := [] }

#guard (analyze unconstrained (10 / (10 / x))).requirements ==
  [.nonzero x, .nonzero (10 / x)]

#guard (analyze unconstrained (ifE (x =ᵍ 0) 1 (10 / x))).requirements == []

#guard (analyze unconstrained (ifE (x <ᵍ 0) (10 / x) 0)).requirements == []

#guard (analyze unconstrained (ifE (x <ᵍ 0) (10 / x) 0)).number ==
  .closed (-10) 0

#guard (analyze unconstrained (ifE (x ≤ᵍ (-1)) (10 / x) 0)).requirements == []

#guard (analyze unconstrained (ifE (x >ᵍ 0) (10 / x) 0)).requirements == []

#guard (analyze unconstrained (ifE (x >ᵍ 0) (10 / x) 0)).number ==
  .closed 0 10

#guard (analyze unconstrained (ifE (x ≥ᵍ 1) (10 / x) 0)).requirements == []

#guard (analyze unconstrained (ifE (x <ᵍ 1) 0 (10 / x))).requirements == []

#guard (analyze unconstrained (ifE (x ≤ᵍ 0) 0 (10 / x))).requirements == []

#guard (analyze unconstrained (ifE (x >ᵍ (-1)) 0 (10 / x))).requirements == []

#guard (analyze unconstrained (ifE (x ≥ᵍ 0) 0 (10 / x))).requirements == []

#guard (analyze unconstrained (ifE (x =ᵍ 0) (10 / (0 : Expr 1)) 1)).requirements ==
  [.nonzero 0]

#guard (analyze unconstrained (x * x)).number == .top

#guard (analyze boundedHundred (x * x)).number == .closed 0 10000

#guard analyze positiveDivisors (100 / (10 / x)) ==
  { number := .closed 20 50, requirements := [] }

#guard analyze (.singleton (.closed 2 20)) (100 / (10 / x)) ==
  { number := .top, requirements := [.nonzero (10 / x)] }

end FreeRangeTest.Analyze
