import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.Matrix.Basic
import Std

structure LinearExpression where
  coeffs : List Int
  lit    : Int
deriving Repr

structure UpdateSystem (n m : ℕ) where
  matrix : Matrix (Fin n) (Fin m) Int
  consts : Vector Int n
--deriving Repr

namespace LinearExpression

def zero : LinearExpression := { coeffs := [], lit := 0 }

def ofLit (n : Int) : LinearExpression := { coeffs := [], lit := n }

def ofVar (i : Nat) : LinearExpression :=
  { coeffs := List.replicate i 0 ++ [1], lit := 0 }

def zipCoeffs (f : Int → Int → Int) (xs ys : List Int) : List Int :=
  match xs, ys with
  | [],      ys      => ys.map (f 0)
  | xs,      []      => xs.map (f · 0)
  | x :: xs, y :: ys => f x y :: zipCoeffs f xs ys

def add (a b : LinearExpression) : LinearExpression :=
  { coeffs := zipCoeffs (· + ·) a.coeffs b.coeffs
  , lit    := a.lit + b.lit }

def sub (a b : LinearExpression) : LinearExpression :=
  { coeffs := zipCoeffs (· - ·) a.coeffs b.coeffs
  , lit    := a.lit - b.lit }

def scale (k : Int) (lf : LinearExpression) : LinearExpression :=
  { coeffs := lf.coeffs.map (· * k)
  , lit    := lf.lit * k }

def mul (a b : LinearExpression) : Option LinearExpression :=
  match a.coeffs.isEmpty, b.coeffs.isEmpty with
  | true,  _    => some (scale a.lit b)
  | _,     true => some (scale b.lit a)
  | false, false => none

-- pad to length n so the list is always predictable
def padTo (n : Nat) (lf : LinearExpression) : LinearExpression :=
  let extra := n - lf.coeffs.length
  { lf with coeffs := lf.coeffs ++ List.replicate extra 0 }

def toCoeff (i : Nat) (lf : LinearExpression) : Int :=
  lf.coeffs.getD i 0

def toLit (lf : LinearExpression) : Int :=
  lf.lit

end LinearExpression

def Expr.toLinearExpression : Expr → Option LinearExpression
  | .lit n     => some (LinearExpression.ofLit n)
  | .var i     => some (LinearExpression.ofVar i)
  | .add e1 e2 => do return LinearExpression.add (← e1.toLinearExpression) (← e2.toLinearExpression)
  | .sub e1 e2 => do return LinearExpression.sub (← e1.toLinearExpression) (← e2.toLinearExpression)
  | .mul e1 e2 => do LinearExpression.mul (← e1.toLinearExpression) (← e2.toLinearExpression)

def Transition.is_self_loop (t : Transition) : Bool :=
  t.src = t.tgt

def IntegerProgams.self_loops (ip : IntegerProgram) : List Transition :=
  ip.edges.filter (fun t => t.is_self_loop)

def Transition._getCoeff (t : Transition) (i j : ℕ) : Option Int := do
  let update ←  t.update[i]?
  let linear ← update.expr.toLinearExpression
  return linear.toCoeff j

def Transition.toUpdateMatrix (t : Transition) (n m : ℕ) : Matrix (Fin n) (Fin m) Int :=
  fun i j => (t._getCoeff i.val j.val).getD 0

-- number of vars, for
def Transition.numVars (t : Transition) : ℕ :=
  t.update.foldl (fun acc u =>
    match u.expr.toLinearExpression with
    | none    => acc
    | some lf => max acc lf.coeffs.length)
  0

def UpdateSystem.ofTransition (t : Transition) (n : ℕ) : UpdateSystem n t.numVars :=
  { matrix := fun i j => (t._getCoeff i.val j.val).getD 0
  , consts := Vector.ofFn (fun i =>
      (t.update[i.val]?.bind (·.expr.toLinearExpression)).map (·.toLit) |>.getD 0)
  }

def Constraint.toLinearExpression (c : Constraint) : Option LinearExpression :=
  match c with
  | .atom .lt lhs rhs => do
      let diff := LinearExpression.sub (← lhs.toLinearExpression) (← rhs.toLinearExpression)
      some { diff with lit := diff.lit + 1 }
  | .atom .eq lhs rhs => do
      some (LinearExpression.sub (← lhs.toLinearExpression) (← rhs.toLinearExpression))
  | .not _   => none
  | .and _ _ => none

structure GuardSystem (m : ℕ) where
  coeffs : Fin m → Int
  lit    : Int

def GuardSystem.ofTransition (t : Transition) : Option (GuardSystem t.numVars) :=do
  let linear ← t.guard.toLinearExpression
  return { coeffs := fun j => linear.toCoeff j.val, lit := linear.toLit }
