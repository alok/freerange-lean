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

#guard AbstractNumber.mul AbstractNumber.top AbstractNumber.top == AbstractNumber.top

example {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) :
    (left.add right).Mem (x + y) :=
  AbstractNumber.mem_add hx hy

example {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) :
    (left.mul right).Mem (x * y) :=
  AbstractNumber.mem_mul hx hy

end FreeRangeTest.Range
