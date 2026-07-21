import FreeRange.Expr

open FreeRange

namespace FreeRangeTest.Expr

def x : Var 1 := .at 0

def five : Env 1 := .singleton 5

def zero : Env 1 := .singleton 0

def x2 : Var 2 := .at 0

def y2 : Var 2 := .at 1

def pair : Env 2 := .ofVector #v[6, 2]

def operatorSurface : List (Expr 2) := [
  x2 + y2, x2 + (y2 + y2), (x2 + x2) + y2,
  x2 - y2, x2 - (y2 + y2), (x2 + x2) - y2,
  x2 * y2, x2 * (y2 + y2), (x2 + x2) * y2,
  x2 / y2, x2 / (y2 + y2), (x2 + x2) / y2
]

#guard ((10 / x : Expr 1).eval five) == some 2

#guard ((10 / x : Expr 1).eval zero) == none

#guard ((10 / x : Expr 1).eval five) == some 2

#guard ((x - 4 : Expr 1).eval five) == some 1

#guard ((ifE (x ≠ᵍ 0) (10 / x) 0).eval five) == some 2

#guard ((ifE (x ≠ᵍ 0) (10 / x) 0).eval zero) == some 0

#guard ((maxE 10 (minE x 90)).eval five) == some 10

#guard operatorSurface.length == 12

#guard ((x2 + y2 : Expr 2).eval pair) == some 8

#guard ((ifE (x2 >ᵍ 0) (maxE x2 (absE y2)) (minE x2 y2)).eval pair) == some 6

#guard (Env.singleton 5) 0 == 5

#guard (Env.uniform (inputCount := 2) 7) 1 == 7

#guard (Context.singleton (.closed 1 3)) 0 == .closed 1 3

#guard (Context.uniform (inputCount := 2) (.atMost 9)) 0 == .atMost 9

#guard (Context.ofVector #v[AbstractNumber.closed 1 3, AbstractNumber.atLeast 4]) 1 ==
  .atLeast 4

end FreeRangeTest.Expr
