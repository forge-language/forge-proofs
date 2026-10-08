import Forge.AST

/-!
# Forge expression semantics

Big-step mathematical-integer evaluator. Division/remainder follow C's
truncation toward zero. Int64 bounds are specified separately in CheckedInt64;
this model alone is not an exact model of the guarded C optimizer.
-/

namespace Forge

open Expr BinOp Value

/-- Evaluate a binary operator on two integer operands. -/
def evalBinInt (op : BinOp) (a b : Int) : Option Value :=
  match op with
  | .add => some (.int (a + b))
  | .sub => some (.int (a - b))
  | .mul => some (.int (a * b))
  | .div => if b = 0 then none else some (.int (a.tdiv b))
  | .mod => if b = 0 then none else some (.int (a.tmod b))
  | .eq  => some (.bool (a = b))
  | .ne  => some (.bool (a ≠ b))
  | .lt  => some (.bool (a < b))
  | .le  => some (.bool (a ≤ b))
  | .gt  => some (.bool (a > b))
  | .ge  => some (.bool (a ≥ b))
  | .and | .or => none

/-- Evaluate a binary operator on two boolean operands. -/
def evalBinBool (op : BinOp) (a b : Bool) : Option Value :=
  match op with
  | .eq  => some (.bool (a = b))
  | .ne  => some (.bool (a ≠ b))
  | .and => some (.bool (a && b))
  | .or  => some (.bool (a || b))
  | _    => none

/-- Big-step evaluation of Forge expressions. -/
def eval : Expr → Option Value
  | .intLit n  => some (.int n)
  | .boolLit b => some (.bool b)
  | .bin op l r => do
      let vl ← eval l
      let vr ← eval r
      match vl, vr with
      | .int a, .int b   => evalBinInt op a b
      | .bool a, .bool b => evalBinBool op a b
      | _, _ => none

/-- Evaluation as an integer (only defined for int-valued expressions). -/
def evalAsInt (e : Expr) : Option Int :=
  match eval e with
  | some (.int n) => some n
  | _ => none

/-- Evaluation as a boolean. -/
def evalAsBool (e : Expr) : Option Bool :=
  match eval e with
  | some (.bool b) => some b
  | _ => none

end Forge
