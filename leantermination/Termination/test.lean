import Mathlib


inductive TExpr where
  | var  : String → TExpr
  | const : Int → TExpr
  | add  : TExpr → TExpr → TExpr
deriving Repr

inductive TCons where
  | lt : TExpr → TExpr → TCons
deriving Repr

def TExpr.vars : TExpr → List String
  | .var v => [v]
  | .const _ => []
  | .add a b => a.vars ++ b.vars

def TCons.vars : TCons → List String
  | .lt a b => a.vars ++ b.vars

def TExpr.toSMT : TExpr → String
  | .var v      => v
  | .const c    => toString c
  | .add a b    =>
      s!"(+ {a.toSMT} {b.toSMT})"

def TCons.toSMT : TCons → String
  | .lt a b =>
      s!"(< {a.toSMT} {b.toSMT})"



def example1 : TCons :=
  TCons.lt
    (.add (.var "x") (.const 3))
    (.add (.var "y") (.const 5))


def TCons.toSMTFile (b : TCons) : String :=
  let vars := b.vars
  let decls :=
    vars.map (fun v => "(declare-const " ++ v ++ " Int)\n")
  let declsStr := decls.foldl (fun acc s => acc ++ s) ""
  "(set-logic QF_LIA)\n\n"
  ++ declsStr ++ "\n"
  ++ "(assert " ++ b.toSMT ++ ")\n"
  ++ "(check-sat)\n"
  ++ "(get-model)\n"


#eval example1
#eval TCons.toSMTFile example1
