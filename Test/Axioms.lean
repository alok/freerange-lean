import FreeRange

/-!
The expected messages make any change to the public theorem trust boundary a compile error.
-/

/--
info: 'FreeRange.analyze_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FreeRange.analyze_sound

/--
info: 'FreeRange.safe_of_no_requirements' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FreeRange.safe_of_no_requirements

namespace FreeRangeTest.Axioms

open FreeRange

def x : Var 1 := .at 0

def unconstrained : Context 1 := .uniform .top

theorem freerange_example :
    Safe unconstrained (ifE (x ≠ᵍ 0) (10 / x) 0) := by
  freerange

/--
info: 'FreeRangeTest.Axioms.freerange_example' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms freerange_example

end FreeRangeTest.Axioms
