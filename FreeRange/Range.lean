import Std

namespace FreeRange

/-- The smaller of two exact integers. -/
def intMin (left right : Int) : Int := if left ≤ right then left else right

/-- The larger of two exact integers. -/
def intMax (left right : Int) : Int := if left ≤ right then right else left

/-- A lower interval endpoint. `negInf` is smaller than every concrete integer. -/
inductive LowerBound where
  | negInf
  | finite (value : Int)
  deriving Repr, DecidableEq, BEq

/-- An upper interval endpoint. `posInf` is larger than every concrete integer. -/
inductive UpperBound where
  | finite (value : Int)
  | posInf
  deriving Repr, DecidableEq, BEq

namespace LowerBound

/-- Whether a lower endpoint admits a concrete integer. -/
def Holds : LowerBound → Int → Prop
  | .negInf, _ => True
  | .finite lower, value => lower ≤ value

instance (bound : LowerBound) (value : Int) : Decidable (bound.Holds value) :=
  match bound with
  | .negInf => inferInstanceAs (Decidable True)
  | .finite lower => inferInstanceAs (Decidable (lower ≤ value))

/-- The smaller of two lower endpoints. -/
def min : LowerBound → LowerBound → LowerBound
  | .negInf, _ | _, .negInf => .negInf
  | .finite left, .finite right => .finite (intMin left right)

/-- The larger of two lower endpoints. -/
def max : LowerBound → LowerBound → LowerBound
  | .negInf, other | other, .negInf => other
  | .finite left, .finite right => .finite (intMax left right)

/-- Add two lower endpoints. -/
def add : LowerBound → LowerBound → LowerBound
  | .negInf, _ | _, .negInf => .negInf
  | .finite left, .finite right => .finite (left + right)

/-- Negate an upper endpoint, turning it into a lower endpoint. -/
def ofNegatedUpper : UpperBound → LowerBound
  | .finite upper => .finite (-upper)
  | .posInf => .negInf

end LowerBound

namespace UpperBound

/-- Whether a concrete integer is below an upper endpoint. -/
def Holds : UpperBound → Int → Prop
  | .finite upper, value => value ≤ upper
  | .posInf, _ => True

instance (bound : UpperBound) (value : Int) : Decidable (bound.Holds value) :=
  match bound with
  | .finite upper => inferInstanceAs (Decidable (value ≤ upper))
  | .posInf => inferInstanceAs (Decidable True)

/-- The smaller of two upper endpoints. -/
def min : UpperBound → UpperBound → UpperBound
  | .posInf, other | other, .posInf => other
  | .finite left, .finite right => .finite (intMin left right)

/-- The larger of two upper endpoints. -/
def max : UpperBound → UpperBound → UpperBound
  | .posInf, _ | _, .posInf => .posInf
  | .finite left, .finite right => .finite (intMax left right)

/-- Add two upper endpoints. -/
def add : UpperBound → UpperBound → UpperBound
  | .posInf, _ | _, .posInf => .posInf
  | .finite left, .finite right => .finite (left + right)

/-- Negate a lower endpoint, turning it into an upper endpoint. -/
def ofNegatedLower : LowerBound → UpperBound
  | .negInf => .posInf
  | .finite lower => .finite (-lower)

end UpperBound

/-- A possibly unbounded closed interval of exact integers. -/
structure Interval where
  lower : LowerBound
  upper : UpperBound
  deriving Repr, DecidableEq, BEq

namespace Interval

/-- The interval containing every integer. -/
def top : Interval := ⟨.negInf, .posInf⟩

/-- A finite closed interval. `lower > upper` represents the empty interval. -/
def closed (lower upper : Int) : Interval := ⟨.finite lower, .finite upper⟩

/-- An interval with only a finite lower bound. -/
def atLeast (lower : Int) : Interval := ⟨.finite lower, .posInf⟩

/-- An interval with only a finite upper bound. -/
def atMost (upper : Int) : Interval := ⟨.negInf, .finite upper⟩

/-- Concrete membership in an interval. -/
def Mem (interval : Interval) (value : Int) : Prop :=
  interval.lower.Holds value ∧ interval.upper.Holds value

instance (interval : Interval) (value : Int) : Decidable (interval.Mem value) :=
  inferInstanceAs (Decidable (interval.lower.Holds value ∧ interval.upper.Holds value))

@[simp] theorem mem_top (value : Int) : top.Mem value := by
  simp [top, Mem, LowerBound.Holds, UpperBound.Holds]

@[simp] theorem mem_closed {lower upper value : Int} :
    (closed lower upper).Mem value ↔ lower ≤ value ∧ value ≤ upper := by
  rfl

/-- The interval hull of two intervals. -/
def join (left right : Interval) : Interval :=
  ⟨left.lower.min right.lower, left.upper.max right.upper⟩

theorem mem_join_left {left right : Interval} {value : Int} (h : left.Mem value) :
    (join left right).Mem value := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower <;> cases leftUpper <;> cases rightLower <;> cases rightUpper <;>
    grind [join, Mem, LowerBound.min, UpperBound.max, LowerBound.Holds,
      UpperBound.Holds, intMin, intMax]

theorem mem_join_right {left right : Interval} {value : Int} (h : right.Mem value) :
    (join left right).Mem value := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower <;> cases leftUpper <;> cases rightLower <;> cases rightUpper <;>
    grind [join, Mem, LowerBound.min, UpperBound.max, LowerBound.Holds,
      UpperBound.Holds, intMin, intMax]

/-- Pointwise interval addition. -/
def add (left right : Interval) : Interval :=
  ⟨left.lower.add right.lower, left.upper.add right.upper⟩

theorem mem_add {left right : Interval} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (add left right).Mem (x + y) := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower <;> cases leftUpper <;> cases rightLower <;> cases rightUpper <;>
    grind [add, Mem, LowerBound.add, UpperBound.add, LowerBound.Holds,
      UpperBound.Holds]

/-- Interval negation. -/
def neg (interval : Interval) : Interval :=
  ⟨.ofNegatedUpper interval.upper, .ofNegatedLower interval.lower⟩

theorem mem_neg {interval : Interval} {value : Int} (h : interval.Mem value) :
    interval.neg.Mem (-value) := by
  rcases interval with ⟨lower, upper⟩
  cases lower <;> cases upper <;>
    grind [neg, Mem, LowerBound.ofNegatedUpper, UpperBound.ofNegatedLower,
      LowerBound.Holds, UpperBound.Holds]

/-- Interval subtraction. -/
def sub (left right : Interval) : Interval := left.add right.neg

theorem mem_sub {left right : Interval} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (sub left right).Mem (x - y) := by
  simpa [sub, Int.sub_eq_add_neg] using mem_add hx (mem_neg hy)

/-- Multiply every member of an interval by a fixed integer. -/
def scale (coefficient : Int) (interval : Interval) : Interval :=
  if coefficient = 0 then
    closed 0 0
  else if 0 < coefficient then
    let lower := match interval.lower with
      | .negInf => .negInf
      | .finite value => .finite (coefficient * value)
    let upper := match interval.upper with
      | .finite value => .finite (coefficient * value)
      | .posInf => .posInf
    ⟨lower, upper⟩
  else
    let lower := match interval.upper with
      | .finite value => .finite (coefficient * value)
      | .posInf => .negInf
    let upper := match interval.lower with
      | .negInf => .posInf
      | .finite value => .finite (coefficient * value)
    ⟨lower, upper⟩

theorem mem_scale {interval : Interval} {coefficient value : Int}
    (h : interval.Mem value) : (scale coefficient interval).Mem (coefficient * value) := by
  by_cases hzero : coefficient = 0
  · subst coefficient
    simp [scale, Mem, closed, LowerBound.Holds, UpperBound.Holds]
  by_cases hpositive : 0 < coefficient
  · have hnonnegative : 0 ≤ coefficient := Int.le_of_lt hpositive
    rcases interval with ⟨lower, upper⟩
    cases lower with
    | negInf =>
        cases upper with
        | finite upper =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact h
        | posInf =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds]
    | finite lower =>
        cases upper with
        | finite upper =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact h
        | posInf =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact h
  · have hnonpositive : coefficient ≤ 0 := by omega
    rcases interval with ⟨lower, upper⟩
    cases lower with
    | negInf =>
        cases upper with
        | finite upper =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact Int.mul_le_mul_of_nonpos_left hnonpositive h
        | posInf =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds]
    | finite lower =>
        cases upper with
        | finite upper =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact ⟨Int.mul_le_mul_of_nonpos_left hnonpositive h.2,
              Int.mul_le_mul_of_nonpos_left hnonpositive h.1⟩
        | posInf =>
            simp [scale, hzero, hpositive, Mem, LowerBound.Holds, UpperBound.Holds] at h ⊢
            exact Int.mul_le_mul_of_nonpos_left hnonpositive h

/-- The least of the four endpoint products for two finite intervals. -/
def productLower (leftLower leftUpper rightLower rightUpper : Int) : Int :=
  intMin (intMin (leftLower * rightLower) (leftLower * rightUpper))
    (intMin (leftUpper * rightLower) (leftUpper * rightUpper))

/-- The greatest of the four endpoint products for two finite intervals. -/
def productUpper (leftLower leftUpper rightLower rightUpper : Int) : Int :=
  intMax (intMax (leftLower * rightLower) (leftLower * rightUpper))
    (intMax (leftUpper * rightLower) (leftUpper * rightUpper))

/-- The standard four-corner interval hull of two finite closed intervals. -/
def productHull (leftLower leftUpper rightLower rightUpper : Int) : Interval :=
  closed (productLower leftLower leftUpper rightLower rightUpper)
    (productUpper leftLower leftUpper rightLower rightUpper)

private theorem productLower_le_leftLower_rightLower (a b c d : Int) :
    productLower a b c d ≤ a * c := by
  grind [productLower, intMin]

private theorem productLower_le_leftLower_rightUpper (a b c d : Int) :
    productLower a b c d ≤ a * d := by
  grind [productLower, intMin]

private theorem productLower_le_leftUpper_rightLower (a b c d : Int) :
    productLower a b c d ≤ b * c := by
  grind [productLower, intMin]

private theorem productLower_le_leftUpper_rightUpper (a b c d : Int) :
    productLower a b c d ≤ b * d := by
  grind [productLower, intMin]

private theorem leftLower_rightLower_le_productUpper (a b c d : Int) :
    a * c ≤ productUpper a b c d := by
  grind [productUpper, intMax]

private theorem leftLower_rightUpper_le_productUpper (a b c d : Int) :
    a * d ≤ productUpper a b c d := by
  grind [productUpper, intMax]

private theorem leftUpper_rightLower_le_productUpper (a b c d : Int) :
    b * c ≤ productUpper a b c d := by
  grind [productUpper, intMax]

private theorem leftUpper_rightUpper_le_productUpper (a b c d : Int) :
    b * d ≤ productUpper a b c d := by
  grind [productUpper, intMax]

/-- Every product of members of two finite intervals lies in their four-corner hull. -/
theorem mem_productHull {a b c d x y : Int}
    (hx : (closed a b).Mem x) (hy : (closed c d).Mem y) :
    (productHull a b c d).Mem (x * y) := by
  change a ≤ x ∧ x ≤ b at hx
  change c ≤ y ∧ y ≤ d at hy
  change productLower a b c d ≤ x * y ∧ x * y ≤ productUpper a b c d
  constructor
  · by_cases hxnonnegative : 0 ≤ x
    · have hxcxy : x * c ≤ x * y :=
        Int.mul_le_mul_of_nonneg_left hy.1 hxnonnegative
      by_cases hcnonnegative : 0 ≤ c
      · exact Int.le_trans (productLower_le_leftLower_rightLower a b c d) <|
          Int.le_trans (Int.mul_le_mul_of_nonneg_right hx.1 hcnonnegative) hxcxy
      · have hcnonpositive : c ≤ 0 := by omega
        exact Int.le_trans (productLower_le_leftUpper_rightLower a b c d) <|
          Int.le_trans (Int.mul_le_mul_of_nonpos_right hx.2 hcnonpositive) hxcxy
    · have hxnonpositive : x ≤ 0 := by omega
      have hxdxy : x * d ≤ x * y :=
        Int.mul_le_mul_of_nonpos_left hxnonpositive hy.2
      by_cases hdnonnegative : 0 ≤ d
      · exact Int.le_trans (productLower_le_leftLower_rightUpper a b c d) <|
          Int.le_trans (Int.mul_le_mul_of_nonneg_right hx.1 hdnonnegative) hxdxy
      · have hdnonpositive : d ≤ 0 := by omega
        exact Int.le_trans (productLower_le_leftUpper_rightUpper a b c d) <|
          Int.le_trans (Int.mul_le_mul_of_nonpos_right hx.2 hdnonpositive) hxdxy
  · by_cases hxnonnegative : 0 ≤ x
    · have hxyd : x * y ≤ x * d :=
        Int.mul_le_mul_of_nonneg_left hy.2 hxnonnegative
      by_cases hdnonnegative : 0 ≤ d
      · exact Int.le_trans hxyd <| Int.le_trans
          (Int.mul_le_mul_of_nonneg_right hx.2 hdnonnegative)
          (leftUpper_rightUpper_le_productUpper a b c d)
      · have hdnonpositive : d ≤ 0 := by omega
        exact Int.le_trans hxyd <| Int.le_trans
          (Int.mul_le_mul_of_nonpos_right hx.1 hdnonpositive)
          (leftLower_rightUpper_le_productUpper a b c d)
    · have hxnonpositive : x ≤ 0 := by omega
      have hxyc : x * y ≤ x * c :=
        Int.mul_le_mul_of_nonpos_left hxnonpositive hy.1
      by_cases hcnonnegative : 0 ≤ c
      · exact Int.le_trans hxyc <| Int.le_trans
          (Int.mul_le_mul_of_nonneg_right hx.2 hcnonnegative)
          (leftUpper_rightLower_le_productUpper a b c d)
      · have hcnonpositive : c ≤ 0 := by omega
        exact Int.le_trans hxyc <| Int.le_trans
          (Int.mul_le_mul_of_nonpos_right hx.1 hcnonpositive)
          (leftLower_rightLower_le_productUpper a b c d)

/-- Interval multiplication, using a four-corner hull when all endpoints are finite. -/
def mul (left right : Interval) : Interval :=
  match left.lower, left.upper, right.lower, right.upper with
  | .finite leftLower, .finite leftUpper, .finite rightLower, .finite rightUpper =>
      productHull leftLower leftUpper rightLower rightUpper
  | _, _, _, _ => top

theorem mem_mul {left right : Interval} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (left.mul right).Mem (x * y) := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower with
  | negInf => simp [mul, top, Mem, LowerBound.Holds, UpperBound.Holds]
  | finite leftLower =>
      cases leftUpper with
      | posInf => simp [mul, top, Mem, LowerBound.Holds, UpperBound.Holds]
      | finite leftUpper =>
          cases rightLower with
          | negInf => simp [mul, top, Mem, LowerBound.Holds, UpperBound.Holds]
          | finite rightLower =>
              cases rightUpper with
              | posInf => simp [mul, top, Mem, LowerBound.Holds, UpperBound.Holds]
              | finite rightUpper =>
                  simpa [mul] using mem_productHull hx hy

/-- Intersect an interval with a finite lower bound. -/
def restrictLower (interval : Interval) (lower : Int) : Interval :=
  ⟨interval.lower.max (.finite lower), interval.upper⟩

theorem mem_restrictLower {interval : Interval} {lower value : Int}
    (hmem : interval.Mem value) (hbound : lower ≤ value) :
    (interval.restrictLower lower).Mem value := by
  rcases interval with ⟨oldLower, upper⟩
  cases oldLower <;> cases upper <;>
    grind [restrictLower, Mem, LowerBound.max, LowerBound.Holds, UpperBound.Holds, intMax]

/-- Intersect an interval with a finite upper bound. -/
def restrictUpper (interval : Interval) (upper : Int) : Interval :=
  ⟨interval.lower, interval.upper.min (.finite upper)⟩

theorem mem_restrictUpper {interval : Interval} {upper value : Int}
    (hmem : interval.Mem value) (hbound : value ≤ upper) :
    (interval.restrictUpper upper).Mem value := by
  rcases interval with ⟨lower, oldUpper⟩
  cases lower <;> cases oldUpper <;>
    grind [restrictUpper, Mem, UpperBound.min, LowerBound.Holds, UpperBound.Holds, intMin]

/-- Interval image of integer minimum. -/
def minimum (left right : Interval) : Interval :=
  ⟨left.lower.min right.lower, left.upper.min right.upper⟩

theorem mem_minimum {left right : Interval} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (minimum left right).Mem (intMin x y) := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower <;> cases leftUpper <;> cases rightLower <;> cases rightUpper <;>
    grind [minimum, Mem, LowerBound.min, UpperBound.min, LowerBound.Holds,
      UpperBound.Holds, intMin]

/-- Interval image of integer maximum. -/
def maximum (left right : Interval) : Interval :=
  ⟨left.lower.max right.lower, left.upper.max right.upper⟩

theorem mem_maximum {left right : Interval} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (maximum left right).Mem (intMax x y) := by
  rcases left with ⟨leftLower, leftUpper⟩
  rcases right with ⟨rightLower, rightUpper⟩
  cases leftLower <;> cases leftUpper <;> cases rightLower <;> cases rightUpper <;>
    grind [maximum, Mem, LowerBound.max, UpperBound.max, LowerBound.Holds,
      UpperBound.Holds, intMax]

/-- Exact integer absolute value, kept explicit for the embedded semantics. -/
def intAbs (value : Int) : Int := if value < 0 then -value else value

/-- Interval image of exact integer absolute value. -/
def absolute (interval : Interval) : Interval :=
  match interval.lower, interval.upper with
  | .negInf, .posInf => atLeast 0
  | .negInf, .finite upper =>
      if upper ≤ 0 then ⟨.finite (-upper), .posInf⟩ else atLeast 0
  | .finite lower, .posInf =>
      if 0 ≤ lower then ⟨.finite lower, .posInf⟩ else atLeast 0
  | .finite lower, .finite upper =>
      if upper ≤ 0 then closed (-upper) (-lower)
      else if 0 ≤ lower then closed lower upper
      else closed 0 (intMax (-lower) upper)

theorem mem_absolute {interval : Interval} {value : Int} (h : interval.Mem value) :
    interval.absolute.Mem (intAbs value) := by
  grind [absolute, intAbs, atLeast, closed, Mem, LowerBound.Holds,
    UpperBound.Holds, intMax]

end Interval

/-- An interval with at most one concrete point removed. -/
structure AbstractNumber where
  interval : Interval
  excluded : Option Int := none
  deriving Repr, DecidableEq, BEq

namespace AbstractNumber

/-- Concrete membership in an abstract number. -/
def Mem (abstract : AbstractNumber) (value : Int) : Prop :=
  abstract.interval.Mem value ∧ abstract.excluded ≠ some value

instance (abstract : AbstractNumber) (value : Int) : Decidable (abstract.Mem value) :=
  inferInstanceAs (Decidable (abstract.interval.Mem value ∧ abstract.excluded ≠ some value))

/-- A canonical abstract number has no exclusion outside its interval. -/
def IsNormalized (abstract : AbstractNumber) : Prop :=
  ∀ value, abstract.excluded = some value → abstract.interval.Mem value

/-- Drop a redundant exclusion without changing the represented set of integers. -/
def normalize (abstract : AbstractNumber) : AbstractNumber :=
  match abstract.excluded with
  | none => abstract
  | some value =>
      if abstract.interval.Mem value then abstract
      else { abstract with excluded := none }

/-- Normalization never changes the interval component. -/
@[simp] theorem normalize_interval (abstract : AbstractNumber) :
    abstract.normalize.interval = abstract.interval := by
  cases hexcluded : abstract.excluded with
  | none => simp [normalize, hexcluded]
  | some excluded =>
      by_cases hin : abstract.interval.Mem excluded <;>
        simp [normalize, hexcluded, hin]

/-- Normalization preserves concrete membership exactly. -/
@[simp] theorem mem_normalize_iff {abstract : AbstractNumber} {value : Int} :
    abstract.normalize.Mem value ↔ abstract.Mem value := by
  cases hexcluded : abstract.excluded with
  | none => simp [normalize, hexcluded]
  | some excluded =>
      by_cases hin : abstract.interval.Mem excluded
      · simp [normalize, hexcluded, hin]
      · have hnormalize :
            abstract.normalize = { abstract with excluded := none } := by
          simp [normalize, hexcluded, hin]
        rw [hnormalize]
        constructor
        · intro hmem
          refine ⟨hmem.1, ?_⟩
          rw [hexcluded]
          intro hequal
          have : excluded = value := Option.some.inj hequal
          subst value
          exact hin hmem.1
        · intro hmem
          exact ⟨hmem.1, by simp⟩

/-- Every normalized result has a useful exclusion, when it has one at all. -/
theorem normalize_isNormalized (abstract : AbstractNumber) : abstract.normalize.IsNormalized := by
  cases hexcluded : abstract.excluded with
  | none =>
      have hnormalize : abstract.normalize = abstract := by
        simp [normalize, hexcluded]
      rw [hnormalize]
      intro value hvalue
      rw [hexcluded] at hvalue
      simp at hvalue
  | some excluded =>
      by_cases hin : abstract.interval.Mem excluded
      · have hnormalize : abstract.normalize = abstract := by
          simp [normalize, hexcluded, hin]
        rw [hnormalize]
        intro value hvalue
        rw [hexcluded] at hvalue
        have : excluded = value := Option.some.inj hvalue
        simpa [this] using hin
      · have hnormalize :
            abstract.normalize = { abstract with excluded := none } := by
          simp [normalize, hexcluded, hin]
        rw [hnormalize]
        intro value hvalue
        simp at hvalue

/-- The abstract number containing every integer. -/
def top : AbstractNumber := ⟨.top, none⟩

/-- A finite closed abstract number. -/
def closed (lower upper : Int) : AbstractNumber := ⟨.closed lower upper, none⟩

/-- An abstract number with only a lower bound. -/
def atLeast (lower : Int) : AbstractNumber := ⟨.atLeast lower, none⟩

/-- An abstract number with only an upper bound. -/
def atMost (upper : Int) : AbstractNumber := ⟨.atMost upper, none⟩

/-- One exact integer. -/
def exact (value : Int) : AbstractNumber := closed value value

/-- Remove one point, replacing any earlier exclusion. -/
def exclude (abstract : AbstractNumber) (value : Int) : AbstractNumber :=
  ({ abstract with excluded := some value }).normalize

/-- Exclusion removes exactly the requested point when it lies in the interval. -/
@[simp] theorem mem_exclude_iff {abstract : AbstractNumber} {excluded value : Int} :
    (abstract.exclude excluded).Mem value ↔
      abstract.interval.Mem value ∧ value ≠ excluded := by
  change ({ abstract with excluded := some excluded } : AbstractNumber).normalize.Mem value ↔ _
  rw [mem_normalize_iff]
  simp [Mem, eq_comm]

/-- Whether the representation proves that a point is absent. -/
def pointExcluded (abstract : AbstractNumber) (value : Int) : Bool :=
  decide (¬ abstract.Mem value)

theorem not_mem_of_pointExcluded {abstract : AbstractNumber} {value : Int}
    (h : abstract.pointExcluded value = true) : ¬ abstract.Mem value := by
  simpa [pointExcluded] using h

/-- Recover a concrete value exactly when the abstract number is a nonempty singleton. -/
def exactValue? (abstract : AbstractNumber) : Option Int :=
  match abstract.interval.lower, abstract.interval.upper with
  | .finite lower, .finite upper =>
      if lower = upper ∧ abstract.excluded ≠ some lower then some lower else none
  | _, _ => none

theorem eq_of_exactValue?_eq_some {abstract : AbstractNumber} {expected value : Int}
    (hexact : abstract.exactValue? = some expected) (hmem : abstract.Mem value) :
    value = expected := by
  grind [exactValue?, Mem, Interval.Mem, LowerBound.Holds, UpperBound.Holds]

/-- Hull two abstract numbers without inventing an excluded point. -/
def join (left right : AbstractNumber) : AbstractNumber :=
  let interval := left.interval.join right.interval
  let excluded :=
    if left.pointExcluded 0 = true ∧ right.pointExcluded 0 = true then some 0
    else if left.excluded = right.excluded then left.excluded
    else none
  (⟨interval, excluded⟩ : AbstractNumber).normalize

theorem mem_join_left {left right : AbstractNumber} {value : Int} (h : left.Mem value) :
    (join left right).Mem value := by
  apply mem_normalize_iff.mpr
  refine ⟨Interval.mem_join_left h.1, ?_⟩
  by_cases hzero : left.pointExcluded 0 = true ∧ right.pointExcluded 0 = true
  · have hleft : left.pointExcluded 0 = true := hzero.1
    have hvalue : value ≠ 0 := by
      intro hvalue
      subst value
      exact not_mem_of_pointExcluded hleft h
    simpa [join, hzero, eq_comm] using hvalue
  · by_cases hequal : left.excluded = right.excluded
    · simpa [join, hzero, hequal] using h.2
    · simp [hzero, hequal]

theorem mem_join_right {left right : AbstractNumber} {value : Int} (h : right.Mem value) :
    (join left right).Mem value := by
  apply mem_normalize_iff.mpr
  refine ⟨Interval.mem_join_right h.1, ?_⟩
  by_cases hzero : left.pointExcluded 0 = true ∧ right.pointExcluded 0 = true
  · have hright : right.pointExcluded 0 = true := hzero.2
    have hvalue : value ≠ 0 := by
      intro hvalue
      subst value
      exact not_mem_of_pointExcluded hright h
    simpa [join, hzero, eq_comm] using hvalue
  · by_cases hequal : left.excluded = right.excluded
    · simpa [join, hzero, hequal] using h.2
    · simp [hzero, hequal]

/-- Abstract negation. -/
def neg (abstract : AbstractNumber) : AbstractNumber :=
  (⟨abstract.interval.neg, abstract.excluded.map (fun value => -value)⟩ : AbstractNumber).normalize

theorem mem_neg {abstract : AbstractNumber} {value : Int} (h : abstract.Mem value) :
    abstract.neg.Mem (-value) := by
  apply mem_normalize_iff.mpr
  refine ⟨Interval.mem_neg h.1, ?_⟩
  cases hexcluded : abstract.excluded with
  | none => simp
  | some excluded =>
      have hne : excluded ≠ value := by simpa [hexcluded] using h.2
      simpa [neg, hexcluded, Int.neg_inj] using hne

private def addExclusion (left right : AbstractNumber) : Option Int :=
  match right.exactValue? with
  | some constant =>
      if left.pointExcluded (-constant) then some 0 else none
  | none =>
      match left.exactValue? with
      | some constant =>
          if right.pointExcluded (-constant) then some 0 else none
      | none => none

/-- Abstract addition, including exact forwarding of a relevant point exclusion. -/
def add (left right : AbstractNumber) : AbstractNumber :=
  (⟨left.interval.add right.interval, addExclusion left right⟩ : AbstractNumber).normalize

theorem mem_add {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (add left right).Mem (x + y) := by
  apply mem_normalize_iff.mpr
  refine ⟨Interval.mem_add hx.1 hy.1, ?_⟩
  change addExclusion left right ≠ some (x + y)
  cases hright : right.exactValue? with
  | some constant =>
      by_cases hpoint : left.pointExcluded (-constant) = true
      · have hyExact : y = constant := eq_of_exactValue?_eq_some hright hy
        have hxNonzero : x ≠ -constant := by
          intro hequal
          subst x
          exact not_mem_of_pointExcluded hpoint hx
        have hsum : x + y ≠ 0 := by omega
        simpa [addExclusion, hright, hpoint, eq_comm] using hsum
      · simp [addExclusion, hright, hpoint]
  | none =>
      cases hleft : left.exactValue? with
      | some constant =>
          by_cases hpoint : right.pointExcluded (-constant) = true
          · have hxExact : x = constant := eq_of_exactValue?_eq_some hleft hx
            have hyNonzero : y ≠ -constant := by
              intro hequal
              subst y
              exact not_mem_of_pointExcluded hpoint hy
            have hsum : x + y ≠ 0 := by omega
            simpa [addExclusion, hright, hleft, hpoint, eq_comm] using hsum
          · simp [addExclusion, hright, hleft, hpoint]
      | none => simp [addExclusion, hright, hleft]

/-- Abstract subtraction. -/
def sub (left right : AbstractNumber) : AbstractNumber := left.add right.neg

theorem mem_sub {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (sub left right).Mem (x - y) := by
  simpa [sub, Int.sub_eq_add_neg] using mem_add hx (mem_neg hy)

/-- Multiply an abstract number by a fixed coefficient. -/
def scale (coefficient : Int) (abstract : AbstractNumber) : AbstractNumber :=
  let excluded :=
    if coefficient ≠ 0 ∧ abstract.pointExcluded 0 = true then some 0 else none
  (⟨abstract.interval.scale coefficient, excluded⟩ : AbstractNumber).normalize

theorem mem_scale {abstract : AbstractNumber} {coefficient value : Int}
    (h : abstract.Mem value) : (scale coefficient abstract).Mem (coefficient * value) := by
  apply mem_normalize_iff.mpr
  refine ⟨Interval.mem_scale h.1, ?_⟩
  by_cases hcoefficient : coefficient = 0
  · subst coefficient
    simp
  by_cases hpoint : abstract.pointExcluded 0 = true
  · have hvalue : value ≠ 0 := by
      intro hvalue
      subst value
      exact not_mem_of_pointExcluded hpoint h
    have hproduct : coefficient * value ≠ 0 := Int.mul_ne_zero hcoefficient hvalue
    simpa [scale, hcoefficient, hpoint, eq_comm] using hproduct
  · simp [hcoefficient, hpoint]

/-- Intersect an abstract number with a finite lower bound. -/
def restrictLower (abstract : AbstractNumber) (lower : Int) : AbstractNumber :=
  ({ abstract with interval := abstract.interval.restrictLower lower }).normalize

theorem mem_restrictLower {abstract : AbstractNumber} {lower value : Int}
    (hmem : abstract.Mem value) (hbound : lower ≤ value) :
    (abstract.restrictLower lower).Mem value := by
  apply mem_normalize_iff.mpr
  exact ⟨Interval.mem_restrictLower hmem.1 hbound, hmem.2⟩

/-- Intersect an abstract number with a finite upper bound. -/
def restrictUpper (abstract : AbstractNumber) (upper : Int) : AbstractNumber :=
  ({ abstract with interval := abstract.interval.restrictUpper upper }).normalize

theorem mem_restrictUpper {abstract : AbstractNumber} {upper value : Int}
    (hmem : abstract.Mem value) (hbound : value ≤ upper) :
    (abstract.restrictUpper upper).Mem value := by
  apply mem_normalize_iff.mpr
  exact ⟨Interval.mem_restrictUpper hmem.1 hbound, hmem.2⟩

private def mulExclusion (left right : AbstractNumber) : Option Int :=
  if left.pointExcluded 0 = true ∧ right.pointExcluded 0 = true then some 0 else none

/-- Abstract multiplication, exact for constants and bounded by the finite four-corner hull. -/
def mul (left right : AbstractNumber) : AbstractNumber :=
  match left.exactValue? with
  | some coefficient => right.scale coefficient
  | none =>
      match right.exactValue? with
      | some coefficient => left.scale coefficient
      | none =>
          (⟨left.interval.mul right.interval, mulExclusion left right⟩ : AbstractNumber).normalize

theorem mem_mul {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (mul left right).Mem (x * y) := by
  cases hleft : left.exactValue? with
  | some coefficient =>
      have hxExact : x = coefficient := eq_of_exactValue?_eq_some hleft hx
      subst x
      simpa [mul, hleft] using (mem_scale (coefficient := coefficient) hy)
  | none =>
      cases hright : right.exactValue? with
      | some coefficient =>
          have hyExact : y = coefficient := eq_of_exactValue?_eq_some hright hy
          subst y
          simpa [mul, hleft, hright, Int.mul_comm] using
            (mem_scale (coefficient := coefficient) hx)
      | none =>
          simp only [mul, hleft, hright]
          apply mem_normalize_iff.mpr
          refine ⟨Interval.mem_mul hx.1 hy.1, ?_⟩
          change mulExclusion left right ≠ some (x * y)
          by_cases hpoints :
              left.pointExcluded 0 = true ∧ right.pointExcluded 0 = true
          · have hxNonzero : x ≠ 0 := by
              intro hzero
              subst x
              exact not_mem_of_pointExcluded hpoints.1 hx
            have hyNonzero : y ≠ 0 := by
              intro hzero
              subst y
              exact not_mem_of_pointExcluded hpoints.2 hy
            have hproduct : x * y ≠ 0 := Int.mul_ne_zero hxNonzero hyNonzero
            simpa [mulExclusion, hpoints, eq_comm] using hproduct
          · simp [mulExclusion, hpoints]

/-- Abstract integer minimum. -/
def minimum (left right : AbstractNumber) : AbstractNumber :=
  ⟨left.interval.minimum right.interval, none⟩

theorem mem_minimum {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (minimum left right).Mem (intMin x y) := by
  exact ⟨Interval.mem_minimum hx.1 hy.1, by simp [minimum]⟩

/-- Abstract integer maximum. -/
def maximum (left right : AbstractNumber) : AbstractNumber :=
  ⟨left.interval.maximum right.interval, none⟩

theorem mem_maximum {left right : AbstractNumber} {x y : Int}
    (hx : left.Mem x) (hy : right.Mem y) : (maximum left right).Mem (intMax x y) := by
  exact ⟨Interval.mem_maximum hx.1 hy.1, by simp [maximum]⟩

/-- Abstract exact-integer absolute value. -/
def absolute (abstract : AbstractNumber) : AbstractNumber :=
  ⟨abstract.interval.absolute, none⟩

theorem mem_absolute {abstract : AbstractNumber} {value : Int} (h : abstract.Mem value) :
    abstract.absolute.Mem (Interval.intAbs value) := by
  exact ⟨Interval.mem_absolute h.1, by simp [absolute]⟩

@[simp] theorem mem_top (value : Int) : top.Mem value := by
  simp [top, Mem, Interval.mem_top]

end AbstractNumber

end FreeRange
