-- Definition of Integer Programs

/-!
  # The Integer Programs

  Integer programs are modeled by a structure closely following the *Definition 2* of this paper: https://arxiv.org/pdf/2202.01769.
  For the strucutre see `IntegerProgram.IntegerProgram`, for dealing with states `IntegerProgram.Env` is necessary.
-/

/- adr
Expr are the representation of polynomials. The constructor Expr.lit constructs an integer value.
The constructor Expr.var constructs a variable, where the natural number decides the indice of the variable xᵢ logically.
Technically it can be used as an array indice, that can be retrieved when providing values to the polynomial.
The definition of polynomials isn't defined as sequence of monomyals but rather, in a recursive tree-like strucutre.
Power products are not defined in the in the core syntax, but rather as derived constructor to keep the inductive definition minimal.
-/

/--
Arbitrary polynomials in the integer domain can be expressed in this format. A sequence of
variables (x₀, x₁, x₂, ...) is assumed and expressed through the constructor `Expr.var`, where
`Expr.var i` denotes xᵢ. For simpler expressiveness `IntegerProgram.Expr.pow` is introduced
to denote power products.

#### Examples

The polynomial `3x₁ - x₀²` can be expressed like this:

```lean
Expr.sub
  (Expr.mul (Expr.lit 3) (Expr.var 1))
  (Expr.mul (Expr.var 0) (Expr.var 0))
```

-/
inductive Expr where
  | lit  : Int → Expr
  | var  : Nat → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
deriving Repr, DecidableEq

/- adr
With this derived constructor you can express power products more easily.
The definition of Expr.pow was made in such way, that it allows the nth-product of arbitrary expression opposed to just variables (Expr.var).
This enables definitions like (x₁ + x₀)² be expressed explicitly.
-/

/--
This derived constructor enables writing power products such as `eⁿ` where `e : Expr` and `n : ℕ` as `Expr e n`.
-/
def Expr.pow (e : Expr) : Nat → Expr
  | 0     => .lit 1
  | n + 1 => .mul e (Expr.pow e n)

/- adr
The definition of value, semantics or states (wording of paper) is through Env, which give variables of polynomials (Expr) their value.
The values are bookkept in a List of integers. Later on in the definitions they become and remain the simple strucutre of semantics, which
provide states of Integer Programs, transitions, equations, ect. with information that can be evaluated. This means that without this semantic
structure all other definitions remain in syntactic nature.
-/

/--
To provide variables of `Expr.var` with variables, `IntegerProgram.Env` can be used to fill a polynomial's variable with integer values.\
The value of `Expr.var[i]` corresponds to `xᵢ` value. For example `Expr.var[3] = 5`, then `x₃ = 5`.
-/
structure Env where
  vars : List Int
deriving Repr, DecidableEq

/- adr
The evaluation of polynomials works with having a syntactic polynomial + Env, which provides the values of the variables.
It returns an Option to be safe for badly-formed states (Env).
-/

/--
To evaluate a polynomial it is necessary to hand a sufficient assignment of variables throught `IntegerProgram.Env`.
If the assignment does not cover all used variables in the polynomial it will return none.
-/
def Expr.eval (expr : Expr) (env : Env) : Option Int :=
  match expr with
  | .lit n    => some n
  | .var n    => env.vars[n]?
  | .add a b  => do pure ((← Expr.eval a env) + (← Expr.eval b env))
  | .sub a b  => do pure ((← Expr.eval a env) - (← Expr.eval b env))
  | .mul a b  => do pure ((← Expr.eval a env) * (← Expr.eval b env))

/-adr
TODO: in a refactoring effort I believe it would be advised to redefine the constructors to be structurally similar to Expr.
It was missed, and seemed to be not worth changing, since lots of proofs would have to be adapted.

The definition of Cmp is short for Comparison and introduces equality and less-than relation.
-/

/--
The base cases of equations are `Cmp.eq` representing equality. And `Cmp.lt` representing less-than. This enables to quantify over polynomials.
-/
inductive Cmp where
  | eq | lt
  deriving Repr, DecidableEq

/- adr
Examples of evaluation function from comparison operators:
The equation `Cmp.eq expr1 expr2 env` evaluates to true, iff `expr1` and `expr2` evaluate to the same integer value.
The equation `Cmp.lt expr1 expr2 env` evaluates to ture, iff `expr1` is strictly smaller than the integer value of `expr2`.
-/

/--
This function evaluats equations and returns a boolean value, if it can be evaluated correcty. This needs two polynomials and a state, which can correctly enable the polynomials to evaluate.
The return type is Option Bool, which is needed when `Expr.eval` fails.
-/
def Cmp.eval (op : Cmp) (a b : Expr) (env : Env) : Option Bool :=
  match op with
  | .eq  => do pure ((← Expr.eval a env) == (← Expr.eval b env))
  | .lt  => do pure ((← Expr.eval a env) < (← Expr.eval b env))

/- adr
This is a strucutre which is used in the paper and the structure that captures the previously defined strucutres into the wanted semantic representation
of having a sequence of simple equations (Cmp).
To receive full autonamy `Constraint.not` makes the boolean operators functionally complete, thus introducing derived constraints such as `Constraint.true`, `Constraint.false` and `Constraint.or`.
-/

/--
This connects equations into constraints which chain lists of compared equations together trough boolean operators.
The base case is `Constraint.atom` which represents one comparison of equations, this can be chained through `Constraint.and` together with other constraints.
-/
inductive Constraint where
  | atom : Cmp → Expr → Expr → Constraint
  | not  : Constraint → Constraint
  | and  : Constraint → Constraint → Constraint
  deriving Repr, DecidableEq

/- adr
Derived Constraint, {¬, ∧} is functionally complete, thus if needed all boolean operators can be derived.
Is necessary, since lots of constraints can simply be True at all times.
-/
def Constraint.or (c1 c2 : Constraint) := Constraint.not (Constraint.and (Constraint.not c1 ) (Constraint.not c2))
def Constraint.true := Constraint.not (Constraint.atom Cmp.lt (Expr.lit 0) (Expr.lit 0))
def Constraint.false := Constraint.not Constraint.true
/-
TODO: these constraints are quite unclean. They all represent equations (Cmp), but since equations have no boolean logic, they can't be directly derived.
Thus Constraint.leq and Cmp.lt exist in unfashionable manner. The only clean solution would be to merge these, yet this is also not clean.
Therefore they currently stay as defined.
-/
def Constraint.gt  (a b : Expr) : Constraint := Constraint.atom .lt b a                    -- a > b  ↔  b < a
def Constraint.geq (a b : Expr) : Constraint := Constraint.not (Constraint.atom .lt a b)   -- a ≥ b  ↔  ¬(a < b)
def Constraint.leq (a b : Expr) : Constraint := Constraint.not (Constraint.atom .lt b a)   -- a ≤ b  ↔  ¬(b < a)

/- adr
The evaluation technique is done with do and pure. do allows to unpack monads value with the arrow-noation.
Example: "← variable" unpacks "some false" to false. If it unpacks to none, then the entire do-block immediatly stops and returns none.
The pure command wraps the normal vlaue into its monadic context.
-/

/--
This function takes a state (`Env`) which provides the underlying polynomials (`Expr`) with values, so that the equations can be evaluated and a boolean value be optained.
-/
def Constraint.eval (c : Constraint) (env : Env) : Option Bool :=
  match c with
  | .atom op e1 e2 => Cmp.eval op e1 e2 env
  | .not c         => do pure !(← c.eval env)
  | .and  c1 c2    => do pure ((← c1.eval env) && (← c2.eval env))


/- adr
Definition of Update function
The definition holds a variable index (Update.pv) and an expression to which is supposed to update the given variable.
-/

/--
This is an update function which can be understood as fᵢ(x₁, ..., xₙ) = xᵢ'. Where xᵢ' is the next value of (post update) so to sepak of xᵢ.
-/
structure Update where
  pv : Nat
  expr : Expr
deriving Repr, DecidableEq

/--
With this function you can receive the updated state (Env), after applying an update to a variable.
-/
def Update.apply (u : Update) (env : Env) : Option Env :=
  do pure { vars := env.vars.set u.pv (← Expr.eval u.expr env) }

/- adr
Returns a new state, in which a list of updates was performed.
This is useful since, a transition can have various update functions (e.g. for various variables).
However if there are multiple updates on the same variable it is important to notice, that this function is non-commutative.
TODO: non-commutativity, could maybe be definied commutatively and fail in case of multiple updates on one variable.
-/

/--
This function performs updates on a list of Update strucutres. Is useful in context of Transitions.
-/
def Update.all (us : List Update) (env : Env) : Option Env :=
  us.foldlM (fun e u => Update.apply u e) env

/--
Based on the paper, this is a representation of transitions. It mirrors the definition as tuple (l, τ, η, l'), where
* l is the source location
* τ is the guard (represented as `Constraint`)
* η is the update function (represented as `List Update`)
* l' is the target location.
-/
structure Transition where
  src : Nat -- l
  tgt : Nat -- l'
  guard : Constraint
  update : List Update -- TODO: updates pv must be unique, read adr of Update.all. (new strucutre Updates or hypothesis)
deriving Repr, DecidableEq

/- adr
Good to notice:
Right now there is no destinction between guards that fail -> none and a failed update -> none.
Maybe introduce a function that evaluates guards explicitly
-/

/--
This is a function that performs the logic of a transition based off of a given state. If the guard accepts this transition for a given state, the updated state is returned.
-/
def Transition.perform (t : Transition) (env : Env) : Option Env := do
  let holds ← Constraint.eval t.guard env
  if !holds then none
  else Update.all t.update env


/- adr
Definition of Integer Programs
- There are should be four invariant constraints:
-- 1. h_strt = the initial location is fixed. Mainly to prevent errors later on.
-- 2. h_locs = the initial location is in the list of locations.
-- 3. h_edges = the transitions are defined on locations of this integer program.
-- 4. h_incom = the initial location doesn't have any incoming edges (constraint in paper)
Currently only h_edges is defined. This reduces overhead and is (currently) the only invariant which is absolutely necessary to close proofs.

-/

/--
This definition is very close to the definition of the paper.
There is a list of locations, which can be considered as a list l₀, l₁, l₂, ...
- The initial location is l₀.
- There is a list of edges, are represented by transitions.
- there is an invariant: h_edges = the transitions are defined on locations of this integer program.
-/
structure IntegerProgram where
  locs : List Nat
  l₀ : Nat -- TODO: this is a little unclean, since it is possible l₀ ∉ locs. maybe replace with h_nonempty or add h_initloc
  edges : List Transition
  h_edges : ∀ t ∈ edges, t.src ∈ locs ∧ t.tgt ∈ locs
deriving Repr, DecidableEq

/- adr
SyntacticPath is an indexed Type, meaning for ever u v : Nat (and every IntegerProgram) SyntacticPath ip u v is its own type.
If SyntacticPath were defined as a Prop, then it would be impossible to compute something like SyntacticPath.length, thus Prop
doesn't work here. On the other hand, defining SyntacticPath as a List wouldn't work, since we counldn't enforce necessary invariants.
The reason it is an indexed type and not a parameterized type is that we can use the endpoints of the path directly without having to
to infere/compute them.
-/

/--
This type of path defines sequences of transitions which do not adhere to guards and update functions.
These paths can move freely on any defined transition. They are constructed through a basecase `nil`
which fixes the end-location of the path. And a recursive case `cons` which can be concatenates a
transition backwards to the list of transitions.
-/
inductive SyntacticPath (ip : IntegerProgram) : Nat → Nat → Type where
  | nil (u : Nat) (h : u ∈ ip.locs) : SyntacticPath ip u u
  | cons {v : Nat} (t : Transition) (h : t ∈ ip.edges)
         (p : SyntacticPath ip t.tgt v) : SyntacticPath ip t.src v

/--
The length of SyntacticPaths are defined through the number transitions performed.
Thus every recursive `cons` case adds one, which is then summed up to be the length.
-/
def SyntacticPath.length {ip : IntegerProgram} {u v : Nat} :
    SyntacticPath ip u v → Nat
  | .nil _ _   => 0
  | .cons _ _ p => 1 + p.length

/--
This indexed type is analog to `SyntacticPath` only that it takes the semantics of transitions into account.
Meaning to construct a step of the path, a transition needs to evaluate its guard to true and provide an assignment Env,
which updates to the linked assignment.
-/
inductive SemanticPath (ip : IntegerProgram) : Env → Nat → Nat → Type where
  | nil (u : Nat) (env : Env) (h : u ∈ ip.locs) : SemanticPath ip env u u
  | cons {v : Nat} (env : Env) (t : Transition) (h : t ∈ ip.edges)
         (hguard : Constraint.eval t.guard env = some true)
         (env' : Env) (hupdate : Update.all t.update env = some env')
         (p : SemanticPath ip env' t.tgt v) : SemanticPath ip env t.src v

/--
The length of SemanticPaths are defined through the number transitions performed.
Thus every recursive `cons` case adds one, which is then summed up to be the length.
-/
def SemanticPath.length {ip : IntegerProgram} {env : Env} {u v : Nat} :
    SemanticPath ip env u v → Nat
  | .nil _ _ _          => 0
  | .cons _ _ _ _ _ _ p => 1 + p.length

/--
This function returns the visited locations of a `SyntacticPath`.
-/
def SyntacticPath.visited {ip : IntegerProgram} {u v : Nat} :
    SyntacticPath ip u v → List Nat
  | .nil u _    => [u]
  | .cons t _ p => t.src :: p.visited

/--
This function returns an equivalent SyntacticPath derived from a SemanticPath.
This function pattern matches the recursive argument to strip the unnecessary Semantics off the transitions.
For the basecase this is simply `Env` but for the recursive case it also includes the guard, update, and sucessor `Env`.
-/
def SemanticPath.toSyntactic {ip : IntegerProgram} {env : Env} {u v : Nat} :
    SemanticPath ip env u v → SyntacticPath ip u v
  | .nil u _ h          => .nil u h
  | .cons _ t h _ _ _ p => .cons t h p.toSyntactic

/--
This is the definition of acyclicity of `IntegerPrograms`.
The way this definition works, it leverages the basecase of a `SyntacticPath` which is path beginnging and ending in the same
location, but without actually being a path which takes transitions. Therefore this definitions says, that any path starting
and ending in the same location has to be exactly this basecase path. Therefore we can ensure that there are no cycles, resulting in
the IntegerPrograms acyclicity.
-/
def IntegerProgram.Acyclic (ip : IntegerProgram) : Prop :=
  ∀ {u : Nat} (p : SyntacticPath ip u u), p.length = 0

/--
This is the definition of Termination of `IntegerPrograms`.
Termination in this case mean, that it **has to** terminate, thus there is no path which is unbound. This definition says exactly this:
for all possible assignments, there is a natural number which bounds every paths length.
-/
def IntegerProgram.Termination (ip : IntegerProgram) : Prop := -- TODO could re-introduce the definition by supremum and show that they coincide.
  ∀ (e : Env), ∃ (n : Nat), ∀ {u v : Nat} (p : SemanticPath ip e u v), p.length ≤ n
