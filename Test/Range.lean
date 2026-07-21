import FreeRange.Range

open FreeRange

namespace FreeRangeTest.Range

#guard AbstractNumber.add (AbstractNumber.closed 1 10) (AbstractNumber.closed 2 3) ==
  AbstractNumber.closed 3 13

#guard AbstractNumber.join (AbstractNumber.closed (-5) (-1)) (AbstractNumber.closed 1 5) ==
  { interval := Interval.closed (-5) 5, excluded := some 0 }

#guard AbstractNumber.sub (AbstractNumber.top.exclude 4) (AbstractNumber.exact 4) ==
  { interval := Interval.top, excluded := some 0 }

#guard AbstractNumber.scale 3 (AbstractNumber.top.exclude 0) ==
  { interval := Interval.top, excluded := some 0 }

#guard AbstractNumber.scale (-3) (AbstractNumber.closed 1 4) ==
  AbstractNumber.closed (-12) (-3)

#guard (AbstractNumber.closed 3 5).exclude 0 == AbstractNumber.closed 3 5

#guard (AbstractNumber.closed 3 5).exclude 4 ==
  { interval := Interval.closed 3 5, excluded := some 4 }

#guard (AbstractNumber.top.exclude 0).restrictLower 3 == AbstractNumber.atLeast 3

#guard ({ interval := Interval.closed 3 5, excluded := some 0 } : AbstractNumber).normalize ==
  AbstractNumber.closed 3 5

#guard AbstractNumber.minimum (AbstractNumber.closed (-5) 10) (AbstractNumber.closed 2 7) ==
  AbstractNumber.closed (-5) 7

#guard AbstractNumber.maximum (AbstractNumber.closed (-5) 10) (AbstractNumber.closed 2 7) ==
  AbstractNumber.closed 2 10

#guard AbstractNumber.absolute (AbstractNumber.closed (-7) 3) ==
  AbstractNumber.closed 0 7

#guard AbstractNumber.mul AbstractNumber.top AbstractNumber.top == AbstractNumber.top

#guard AbstractNumber.mul (AbstractNumber.closed 1 4) (AbstractNumber.closed 2 3) ==
  AbstractNumber.closed 2 12

#guard AbstractNumber.mul (AbstractNumber.closed 1 4) (AbstractNumber.closed (-3) (-2)) ==
  AbstractNumber.closed (-12) (-2)

#guard AbstractNumber.mul (AbstractNumber.closed (-4) (-1)) (AbstractNumber.closed 2 3) ==
  AbstractNumber.closed (-12) (-2)

#guard AbstractNumber.mul (AbstractNumber.closed (-4) (-1))
    (AbstractNumber.closed (-3) (-2)) == AbstractNumber.closed 2 12

#guard AbstractNumber.mul (AbstractNumber.closed (-2) 3) (AbstractNumber.closed (-4) 5) ==
  AbstractNumber.closed (-12) 15

#guard AbstractNumber.mul (AbstractNumber.atLeast 1) (AbstractNumber.closed 2 3) ==
  { interval := Interval.top, excluded := some 0 }

#guard AbstractNumber.mul (AbstractNumber.top.exclude 0) (AbstractNumber.top.exclude 0) ==
  { interval := Interval.top, excluded := some 0 }

#guard AbstractNumber.mul (AbstractNumber.top.exclude 0) AbstractNumber.top ==
  AbstractNumber.top

#guard AbstractNumber.mul (AbstractNumber.exact (-3)) (AbstractNumber.closed 1 4) ==
  AbstractNumber.closed (-12) (-3)

#guard AbstractNumber.ediv (AbstractNumber.closed 10 20) (AbstractNumber.closed 2 5) ==
  AbstractNumber.closed 2 10

#guard AbstractNumber.ediv (AbstractNumber.closed (-20) (-10))
    (AbstractNumber.closed 2 5) == AbstractNumber.closed (-10) (-2)

#guard AbstractNumber.ediv (AbstractNumber.closed 10 20)
    (AbstractNumber.closed (-5) (-2)) == AbstractNumber.closed (-10) (-2)

#guard AbstractNumber.ediv (AbstractNumber.closed (-20) (-10))
    (AbstractNumber.closed (-5) (-2)) == AbstractNumber.closed 2 10

#guard AbstractNumber.ediv (AbstractNumber.closed (-10) 20)
    (AbstractNumber.closed 2 5) == AbstractNumber.closed (-5) 10

#guard AbstractNumber.ediv (AbstractNumber.closed 10 20) (AbstractNumber.atLeast 2) ==
  AbstractNumber.closed 0 10

#guard AbstractNumber.ediv (AbstractNumber.closed 10 20) (AbstractNumber.atMost (-2)) ==
  AbstractNumber.closed (-10) 0

#guard AbstractNumber.ediv (AbstractNumber.closed (-20) (-10))
    (AbstractNumber.atLeast 2) == AbstractNumber.closed (-10) 0

#guard AbstractNumber.ediv (AbstractNumber.atLeast 1) (AbstractNumber.exact 2) ==
  AbstractNumber.atLeast 0

#guard AbstractNumber.ediv (AbstractNumber.atLeast 1) (AbstractNumber.exact (-2)) ==
  AbstractNumber.atMost 0

#guard AbstractNumber.ediv (AbstractNumber.atMost (-1)) (AbstractNumber.exact 2) ==
  AbstractNumber.atMost (-1)

#guard AbstractNumber.ediv AbstractNumber.top (AbstractNumber.exact 2) ==
  AbstractNumber.top

#guard AbstractNumber.ediv (AbstractNumber.closed 1 10)
    (AbstractNumber.closed (-2) 3) == AbstractNumber.top

#guard AbstractNumber.ediv (AbstractNumber.closed 1 10)
    ((AbstractNumber.closed (-2) 3).exclude 0) == AbstractNumber.top

#guard AbstractNumber.ediv (AbstractNumber.top.exclude 4) (AbstractNumber.exact 1) ==
  AbstractNumber.top.exclude 4

#guard AbstractNumber.ediv (AbstractNumber.top.exclude 4) (AbstractNumber.exact (-1)) ==
  AbstractNumber.top.exclude (-4)

#guard AbstractNumber.ediv (AbstractNumber.top.exclude 4) (AbstractNumber.exact 2) ==
  AbstractNumber.top

example :
    (Interval.mul (Interval.closed (-2) 3) (Interval.closed (-4) 5)).Mem (3 * (-4)) :=
  Interval.mem_mul (by decide) (by decide)

example (number : AbstractNumber) : number.normalize.IsNormalized :=
  AbstractNumber.normalize_isNormalized number

example (number : AbstractNumber) (value : Int) :
    number.normalize.Mem value ↔ number.Mem value :=
  AbstractNumber.mem_normalize_iff

example {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) :
    (left.add right).Mem (x + y) :=
  AbstractNumber.mem_add hx hy

example {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) :
    (left.mul right).Mem (x * y) :=
  AbstractNumber.mem_mul hx hy

example :
    (Interval.ediv (Interval.closed 10 20) (Interval.closed 2 5)).Mem (17 / 4) :=
  Interval.mem_ediv (by decide) (by decide)

example :
    (Interval.ediv (Interval.closed 10 20) (Interval.atLeast 2)).Mem (17 / 100) :=
  Interval.mem_ediv (by decide) (by decide)

example :
    (Interval.ediv (Interval.atLeast 1) (Interval.closed (-2) (-2))).Mem (3 / (-2)) :=
  Interval.mem_ediv (by decide) (by decide)

example {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) :
    (left.ediv right).Mem (x / y) :=
  AbstractNumber.mem_ediv hx hy

end FreeRangeTest.Range
