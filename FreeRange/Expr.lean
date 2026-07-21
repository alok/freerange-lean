import FreeRange.Range

namespace FreeRange

/-- The six input-to-constant comparisons supported by branch refinement. -/
inductive Comparison where
  /-- Integer equality. -/
  | eq
  /-- Integer disequality. -/
  | ne
  /-- Strict less-than. -/
  | lt
  /-- Non-strict less-than. -/
  | le
  /-- Strict greater-than. -/
  | gt
  /-- Non-strict greater-than. -/
  | ge
  deriving Repr, DecidableEq, BEq

namespace Comparison

/-- Concrete exact-integer meaning of a comparison. -/
def Holds : Comparison → Int → Int → Prop
  | .eq, left, right => left = right
  | .ne, left, right => left ≠ right
  | .lt, left, right => left < right
  | .le, left, right => left ≤ right
  | .gt, left, right => left > right
  | .ge, left, right => left ≥ right

instance (comparison : Comparison) (left right : Int) :
    Decidable (comparison.Holds left right) :=
  match comparison with
  | .eq => inferInstanceAs (Decidable (left = right))
  | .ne => inferInstanceAs (Decidable (left ≠ right))
  | .lt => inferInstanceAs (Decidable (left < right))
  | .le => inferInstanceAs (Decidable (left ≤ right))
  | .gt => inferInstanceAs (Decidable (left > right))
  | .ge => inferInstanceAs (Decidable (left ≥ right))

end Comparison

/-- A guard compares one input with a fixed exact integer. -/
structure Guard (inputCount : Nat) where
  /-- The input inspected by the guard. -/
  input : Fin inputCount
  /-- The comparison applied to the input and constant. -/
  comparison : Comparison
  /-- The exact integer on the right-hand side. -/
  constant : Int
  deriving Repr, DecidableEq, BEq

/-- The embedded exact-integer expression language analyzed by FreeRange. -/
inductive Expr (inputCount : Nat) where
  /-- An exact integer constant. -/
  | const (value : Int)
  /-- One input selected by its finite index. -/
  | input (index : Fin inputCount)
  /-- Integer negation. -/
  | neg (value : Expr inputCount)
  /-- Integer addition. -/
  | add (left right : Expr inputCount)
  /-- Integer subtraction. -/
  | sub (left right : Expr inputCount)
  /-- Integer multiplication. -/
  | mul (left right : Expr inputCount)
  /-- Partial integer division, undefined when the divisor is zero. -/
  | div (dividend divisor : Expr inputCount)
  /-- Integer minimum. -/
  | minimum (left right : Expr inputCount)
  /-- Integer maximum. -/
  | maximum (left right : Expr inputCount)
  /-- Exact integer absolute value. -/
  | absolute (value : Expr inputCount)
  /-- A conditional selected by an input-to-constant guard. -/
  | ite (guard : Guard inputCount) (thenBranch elseBranch : Expr inputCount)
  deriving Repr, DecidableEq, BEq

/-- One named input for readable expression and guard construction. -/
structure Var (inputCount : Nat) where
  /-- The corresponding input index. -/
  index : Fin inputCount
  deriving Repr, DecidableEq, BEq

namespace Var

/-- Construct a variable from its finite input index. -/
def «at» (index : Fin inputCount) : Var inputCount := ⟨index⟩

/-- Use a variable as an embedded expression. -/
def expr (inputVar : Var inputCount) : Expr inputCount := .input inputVar.index

/-- Compare a variable with an exact integer. -/
def guard (inputVar : Var inputCount) (comparison : Comparison) (constant : Int) :
    Guard inputCount :=
  ⟨inputVar.index, comparison, constant⟩

instance : Coe (Var inputCount) (Expr inputCount) := ⟨expr⟩

end Var

instance (value : Nat) : OfNat (Expr inputCount) value where
  ofNat := .const (Int.ofNat value)

instance : Neg (Expr inputCount) where
  neg := .neg

instance : HAdd (Expr inputCount) (Expr inputCount) (Expr inputCount) where
  hAdd := .add

instance : HSub (Expr inputCount) (Expr inputCount) (Expr inputCount) where
  hSub := .sub

instance : HMul (Expr inputCount) (Expr inputCount) (Expr inputCount) where
  hMul := .mul

instance : HDiv (Expr inputCount) (Expr inputCount) (Expr inputCount) where
  hDiv := .div

instance : HAdd (Var inputCount) (Var inputCount) (Expr inputCount) where
  hAdd := fun left right => .add left.expr right.expr

instance : HAdd (Var inputCount) (Expr inputCount) (Expr inputCount) where
  hAdd := fun left right => .add left.expr right

instance : HAdd (Expr inputCount) (Var inputCount) (Expr inputCount) where
  hAdd := fun left right => .add left right.expr

instance : HSub (Var inputCount) (Var inputCount) (Expr inputCount) where
  hSub := fun left right => .sub left.expr right.expr

instance : HSub (Var inputCount) (Expr inputCount) (Expr inputCount) where
  hSub := fun left right => .sub left.expr right

instance : HSub (Expr inputCount) (Var inputCount) (Expr inputCount) where
  hSub := fun left right => .sub left right.expr

instance : HMul (Var inputCount) (Var inputCount) (Expr inputCount) where
  hMul := fun left right => .mul left.expr right.expr

instance : HMul (Var inputCount) (Expr inputCount) (Expr inputCount) where
  hMul := fun left right => .mul left.expr right

instance : HMul (Expr inputCount) (Var inputCount) (Expr inputCount) where
  hMul := fun left right => .mul left right.expr

instance : HDiv (Var inputCount) (Var inputCount) (Expr inputCount) where
  hDiv := fun left right => .div left.expr right.expr

instance : HDiv (Var inputCount) (Expr inputCount) (Expr inputCount) where
  hDiv := fun left right => .div left.expr right

instance : HDiv (Expr inputCount) (Var inputCount) (Expr inputCount) where
  hDiv := fun left right => .div left right.expr

/-- Build a guard that tests equality with a constant. -/
infix:50 " =ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.eq constant

/-- Build a guard that tests disequality with a constant. -/
infix:50 " ≠ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.ne constant

/-- Build a guard that tests strict inequality with a constant. -/
infix:50 " <ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.lt constant

/-- Build a guard that tests non-strict inequality with a constant. -/
infix:50 " ≤ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.le constant

/-- Build a guard that tests strict greater-than with a constant. -/
infix:50 " >ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.gt constant

/-- Build a guard that tests non-strict greater-than with a constant. -/
infix:50 " ≥ᵍ " => fun inputVar constant => Var.guard inputVar Comparison.ge constant

/-- An embedded conditional expression. -/
def ifE (guard : Guard inputCount) (thenBranch elseBranch : Expr inputCount) :
    Expr inputCount :=
  .ite guard thenBranch elseBranch

/-- Embedded exact-integer minimum. -/
def minE (left right : Expr inputCount) : Expr inputCount := .minimum left right

/-- Embedded exact-integer maximum. -/
def maxE (left right : Expr inputCount) : Expr inputCount := .maximum left right

/-- Embedded exact-integer absolute value. -/
def absE (value : Expr inputCount) : Expr inputCount := .absolute value

/-- A concrete assignment to every expression input. -/
abbrev Env (inputCount : Nat) := Fin inputCount → Int

/-- An abstract range for every expression input. -/
abbrev Context (inputCount : Nat) := Fin inputCount → AbstractNumber

namespace Env

/-- Assign the same concrete integer to every input. -/
def uniform (value : Int) : Env inputCount := fun _ => value

/-- A one-input concrete environment. -/
def singleton (value : Int) : Env 1 := fun _ => value

/-- Build a concrete environment from an exactly sized vector. -/
def ofVector (values : Vector Int inputCount) : Env inputCount := values.get

end Env

namespace Context

/-- Assign the same abstract number to every input. -/
def uniform (number : AbstractNumber) : Context inputCount := fun _ => number

/-- A one-input abstract context. -/
def singleton (number : AbstractNumber) : Context 1 := fun _ => number

/-- Build an abstract context from an exactly sized vector. -/
def ofVector (numbers : Vector AbstractNumber inputCount) : Context inputCount := numbers.get

end Context

namespace Guard

/-- Whether a concrete environment takes a guard's true branch. -/
def Holds (guard : Guard inputCount) (environment : Env inputCount) : Prop :=
  guard.comparison.Holds (environment guard.input) guard.constant

instance (guard : Guard inputCount) (environment : Env inputCount) :
    Decidable (guard.Holds environment) :=
  inferInstanceAs (Decidable (guard.comparison.Holds (environment guard.input) guard.constant))

end Guard

namespace Expr

/-- Evaluate an embedded expression. Division by zero is the only failure. -/
def eval (environment : Env inputCount) : Expr inputCount → Option Int
  | .const value => some value
  | .input index => some (environment index)
  | .neg value => return -(← value.eval environment)
  | .add left right => return (← left.eval environment) + (← right.eval environment)
  | .sub left right => return (← left.eval environment) - (← right.eval environment)
  | .mul left right => return (← left.eval environment) * (← right.eval environment)
  | .div dividend divisor => do
      let dividendValue ← dividend.eval environment
      let divisorValue ← divisor.eval environment
      if divisorValue = 0 then none else some (dividendValue / divisorValue)
  | .minimum left right => return intMin (← left.eval environment) (← right.eval environment)
  | .maximum left right => return intMax (← left.eval environment) (← right.eval environment)
  | .absolute value => return Interval.intAbs (← value.eval environment)
  | .ite guard thenBranch elseBranch =>
      if guard.Holds environment then thenBranch.eval environment else elseBranch.eval environment

end Expr

namespace Context

/-- A context covers an environment when every concrete input inhabits its abstract range. -/
def Covers (context : Context inputCount) (environment : Env inputCount) : Prop :=
  ∀ index, (context index).Mem (environment index)

end Context

/-- An expression is safe under a context when evaluation succeeds for every covered environment. -/
def Safe (context : Context inputCount) (expression : Expr inputCount) : Prop :=
  ∀ environment, context.Covers environment → ∃ value, expression.eval environment = some value

end FreeRange
