import leantermination.Datastructures.IntegerProgram
import leantermination.Termination.linear_expression
open IntegerProgram

set_option linter.style.longLine false

structure FarkasVars (n : ℕ) where
  a : Vector String n
  lambda : String
  deriving Repr

inductive SMTExpr where
  | var   : String → SMTExpr
  | int   : Int → SMTExpr
  | add   : SMTExpr → SMTExpr → SMTExpr
  | mul   : SMTExpr → SMTExpr → SMTExpr
  | leq   : SMTExpr → SMTExpr → SMTExpr
  | eq    : SMTExpr → SMTExpr → SMTExpr

def SMTExpr.toZ3 : SMTExpr → String
  | .var s     => s
  | .int n     => toString n
  | .add a b   => s!"(+ {a.toZ3} {b.toZ3})"
  | .mul a b   => s!"(* {a.toZ3} {b.toZ3})"
  | .leq a b   => s!"(<= {a.toZ3} {b.toZ3})"
  | .eq  a b   => s!"(= {a.toZ3} {b.toZ3})"

-- aᵀv = a0*v0 + a1*v1 + ... + an-1*vn-1
def FerkasVars.dotProduct (a : Vector String n) (v : Fin n → Int) : SMTExpr :=
  (List.finRange n).foldl (fun acc i =>
    .add acc (.mul (.var (a.get i)) (.int (v i))))
  (.int 0)

def FarkasVars.ofSize (n : ℕ) : FarkasVars n :=
  { a      := Vector.ofFn (fun i => s!"a{i.val}")
  , lambda := "lambda" }

    -- condition 1: for each column j, aᵀ(M - I)_j = λ * c_j
def farkasCoeffConstraints (sys : UpdateSystem n m) (c : Fin m → Int)
    (vars : FarkasVars n) : List SMTExpr :=
  List.finRange m |>.map fun j =>
    let mMinusI_col := fun i => sys.matrix i j - if i.val == j.val then 1 else 0
    .eq (FerkasVars.dotProduct vars.a mMinusI_col)
        (.mul (.var vars.lambda) (.int (c j)))

-- condition 2: aᵀc₀ ≤ -1 + λ*d
def farkasConstConstraint (sys : UpdateSystem n m) (d : Int)
    (vars : FarkasVars n) : SMTExpr :=
  .leq (FerkasVars.dotProduct vars.a (fun i => sys.consts.get i))
       (.add (.int (-1)) (.mul (.var vars.lambda) (.int d)))

-- condition 3: λ ≥ 0
def farkasLambdaConstraint (vars : FarkasVars n) : SMTExpr :=
  .leq (.int 0) (.var vars.lambda)

def farkasConstraints (sys : UpdateSystem n m) (c : Fin m → Int) (d : Int)
    (vars : FarkasVars n) : List SMTExpr :=
  farkasCoeffConstraints sys c vars ++
  [farkasConstConstraint sys d vars,
   farkasLambdaConstraint vars]

def toSMT2 (sys : UpdateSystem n m) (c : Fin m → Int) (d : Int) : String :=
  let vars := FarkasVars.ofSize n
  let constraints := farkasConstraints sys c d vars
  -- declarations
  let decls :=
    (List.range n).map (fun i => s!"(declare-const a{i} Int)") ++
    ["(declare-const lambda Int)"]
  -- asserts
  let asserts := constraints.map (fun e => s!"(assert {e.toZ3})")
  -- join everything
  [ "(set-logic QF_LIA)"
  , ""
  ] ++ decls ++
  [ ""
  ] ++ asserts ++
  [ ""
  , "(check-sat)"
  , "(get-model)"
  ] |> String.intercalate "\n"

def Transition.toSMT (t : Transition) : String :=
  let updateSys : UpdateSystem (List.length t.update) t.numVars := UpdateSystem.ofTransition t (List.length t.update)
  match GuardSystem.ofTransition t with
  | none   => "(error \"non-linear or unsupported guard\")"
  | some g => toSMT2 updateSys g.coeffs g.lit
