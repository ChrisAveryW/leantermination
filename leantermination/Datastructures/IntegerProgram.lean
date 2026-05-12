-- Definition of Integer Programs

-- Definition of Polynomials
-- Expr.lit 5 refers to the integer value 5. Expr.var 5 refers to the variable x₅.
-- A variable stream of x₀, x₁, x₂, ... is assumed (there are no other variables, like y, z,...)
inductive Expr where
  | lit  : Int → Expr
  | var  : Nat → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
deriving Repr, DecidableEq

-- Derived Expressions
def Expr.pow (e : Expr) : Nat → Expr
  | 0     => .lit 1
  | n + 1 => .mul e (Expr.pow e n)

-- Definition of States
-- these provide Expr.var's with values.
-- e.g. Env.vars[0] correspond to the value of x₀.
structure Env where
  vars : List Int
deriving Repr, DecidableEq

-- Evaluation of Expression
-- The evaluation always works with a provided state
-- TODO: currently an invalid matching between State and Expression could is handeld through a
--       quick fix: by defining all values that don't match to -1. This should be replaced by an invariant or Option Type
def Expr.eval (expr : Expr) (env : Env) : Option Int :=
  match expr with
  | .lit n    => some n
  | .var n    => env.vars[n]?
  | .add a b  => do pure ((← Expr.eval a env) + (← Expr.eval b env))
  | .sub a b  => do pure ((← Expr.eval a env) - (← Expr.eval b env))
  | .mul a b  => do pure ((← Expr.eval a env) * (← Expr.eval b env))


-- Comparison Operators
inductive Cmp where
  | eq | lt
  deriving Repr, DecidableEq

def Cmp.eval (op : Cmp) (a b : Expr) (env : Env) : Option Bool :=
  match op with
  | .eq  => do pure ((← Expr.eval a env) == (← Expr.eval b env))
  | .lt  => do pure ((← Expr.eval a env) < (← Expr.eval b env))

-- Derived Comparison Operators
-- TODO: they will be evaluated directly so they aren't syntactic definitions at all, is it possible to create these definitions syntactically?
def Cmp.gt (a b : Expr) (env : Env) : Option Bool := Cmp.eval .lt b a env   -- a > b  ↔  b < a
def Cmp.geq (a b : Expr) (env : Env) : Option Bool := do pure !(← Cmp.eval .lt a b env) -- a ≥ b  ↔  ¬(a < b)
def Cmp.leq (a b : Expr) (env : Env) : Option Bool := do pure !(← Cmp.eval .lt b a env) -- a ≤ b  ↔  ¬(b < a)

-- Constraints are either atomic comparisons or logical combinations
inductive Constraint where
  | atom : Cmp → Expr → Expr → Constraint
  | not  : Constraint → Constraint
  | and  : Constraint → Constraint → Constraint
  deriving Repr, DecidableEq

-- Derived Constraint, {¬, ∧} is functionally complete, thus if needed all boolean operators can be derived
def Constraint.or (c1 c2 : Constraint) := Constraint.not
(Constraint.and (Constraint.not c1 ) (Constraint.not c2))

def Constraint.true := Constraint.not (Constraint.atom Cmp.lt (Expr.lit 0) (Expr.lit 0))
def Constraint.false := Constraint.not Constraint.true


def Constraint.eval (c : Constraint) (env : Env) : Option Bool :=
  match c with
  | .atom op e1 e2 => Cmp.eval op e1 e2 env
  | .not c         => do pure !(← c.eval env)
  | .and  c1 c2    => do pure ((← c1.eval env) && (← c2.eval env))


-- Definition of Update function
-- The definition holds a variable (pv) and an expression to which the pv is updated to.
structure Update where
  pv : Nat
  expr : Expr
deriving Repr, DecidableEq

-- Returns the new state, which was effected by the update function.
def Update.apply (u : Update) (env : Env) : Option Env :=
  do pure { vars := env.vars.set u.pv (← Expr.eval u.expr env) }

-- Returns a new state, in which a list of updates was performed.
-- This is useful since, a transition can have various update functions (e.g. for various variables)
def Update.all (us : List Update) (env : Env) : Option Env :=
  us.foldlM (fun e u => Update.apply u e) env

-- Definition of Transitions
structure Transition where
  src : Nat -- l
  tgt : Nat -- l'
  guard : Constraint
  update : List Update -- TODO: updates pv must be unique!!!
deriving Repr, DecidableEq

-- Returns a tuple which describes if a transition was possible to perform,
-- given the constraint of a guard and state.
-- I chose to add the a variable determining if the transition was successful,
-- instead of just returning the same state to prevent errors in termination proofs.
-- TODO: maybe use Options, which could be cleaner
def Transition.perform (t : Transition) (env : Env) : Option Env := do
  let holds ← Constraint.eval t.guard env
  if !holds then none
  else Update.all t.update env


-- Definition of Integer Programs
-- This definition is very near to the definition of the paper.
-- There is a list of locations, which can be considered as a list l₀, l₁, l₂, ...
-- The initial location is l₀.
-- There is a list of edges, are represented by transitions.
-- There are four invariant constraints:
-- 1. h_strt = the initial location is fixed. Mainly to prevent errors later on.
-- 2. h_locs = the initial location is in the list of locations.
-- 3. h_edges = the transitions are defined on locations of this integer program.
-- 4. h_incom = the initial location doesn't have any incoming edges (constraint in paper)

structure IntegerProgram where
  locs : List Nat
  l₀ : Nat
  edges : List Transition
  h_edges : ∀ t ∈ edges, t.src ∈ locs ∧ t.tgt ∈ locs
deriving Repr, DecidableEq

inductive IPPath (ip : IntegerProgram) : Nat → Nat → Type where
     | nil  : (u : Nat) → u ∈ ip.locs → IPPath ip u u
     | cons : {v : Nat} → (t : Transition) → t ∈ ip.edges →
              IPPath ip t.tgt v → IPPath ip t.src v

def IPPath.length {ip : IntegerProgram} {u v : Nat} :
    IPPath ip u v → Nat
  | .nil _ _   => 0
  | .cons _ _ p => 1 + p.length

def IntegerProgram.Acyclic (ip : IntegerProgram) : Prop :=
  ∀ {u : Nat} (p : IPPath ip u u), p.length = 0


/-
-- Functions for Ineger Programs
-- currently not in usage
def IntegerProgram.avail_trans (ip : IntegerProgram) (loc : Nat) : List Transition :=
  ip.edges.filter (fun tr => tr.src == loc)

def IntegerProgram.succs (ip : IntegerProgram) (loc : Nat) : List Nat :=
  (ip.edges.filter (fun tr => tr.src == loc)).map (fun tr => tr.tgt)



-- Definition of Configuration
-- A Configuration is the combination of a location with a state (Loc × State)
-- (This is always regarding an Integer Program.)
structure Configuration where
  loc : Nat
  env : Env
  prog: IntegerProgram
deriving Repr, DecidableEq

-- Definition of an empty Configuration, which is sometimes useful.
def empty_configuration : Configuration :=
  {loc := 0, env := {vars := []}, prog:=
  {locs := [0], l₀ := 0, edges := [],
   h_strt := by decide,
   h_locs := by decide,
   h_trans := by decide,
   h_incom := by decide}}

-- Definition of some functions on Configurations
-- They are not in usage currently
def Configuration.env_avail_trans (ip : IntegerProgram) (loc : Nat) (env : Env) : List Transition :=
  ip.edges.filter (fun tr => tr.src == loc && Constraint.eval tr.guard env)

def Configuration.env_succs (ip : IntegerProgram) (loc : Nat) (env : Env) : List Nat :=
  (ip.edges.filter (fun tr => tr.src == loc && Constraint.eval tr.guard env)).map (fun tr => tr.tgt)

-- Definition of a Natural Number with Infinity
-- Not in usage, using Mathlib for this functionality: ℕ∞
inductive ExtNat where
  | fin : Nat → ExtNat
  | inf : ExtNat
deriving Repr

-- Definition of order for the Natural Numbers with Infinity
def ExtNat.max : ExtNat → ExtNat → ExtNat
  | .inf, _ => .inf
  | _, .inf => .inf
  | .fin a, .fin b => .fin (Nat.max a b)

-- Calculation of Configuration Step
-- Returns the next configuration, if you perform a valid transition.
-- Here in the case of a step, which doesn't make sense an empty_configuration is returned.
-- TODO: replace the empty_configuration with invariant or Option.
def Configuration.step_computation (c : Configuration) (t : Transition) : Configuration :=
  if t ∈ c.prog.edges && t.src == c.loc then
    let res := (Transition.perform t c.env)
    if res.1 then
      {loc := t.tgt, env := res.2, prog := c.prog}
    else
      empty_configuration
  else
    empty_configuration

-- Definition of Configuration Step
-- This definition is used for proofs not for algorithmic functions.
-- does (lₜ,σ) → (lₜ',σ') hold with transition t=(lₜ, τ, η, l'ₜ)
def Configuration.step (c1 : Configuration) (c2 : Configuration) : Prop :=
  (c1.prog = c2.prog) ∧ -- c1,c2 are definied on the same Integer Program
  ∃ t ∈ c1.prog.edges,
    (Constraint.eval t.guard c1.env) ∧ -- σ(τ) = true
  (c2.env = Update.all t.update c1.env) ∧ -- v ∈ PV we have σ(η(v)) = σ'(v)
  (t.src = c1.loc ∧ t.tgt = c2.loc)-- l = lₜ and l' = l'ₜ


-- Definition of Paths
-- This definition represents "is there a path of the length n, which starts in a and ends in b" (a, b are Configurations)
-- expressed differently: does (l,σ) →ᵏ (l',σ') hold for a specific k ∈ ℕ
def Configuration.pathN : Nat → Configuration → Configuration →  Prop
    | 0,    _, _ => False
    | n + 1,c1, c2 => Configuration.step c1 c2 ∨
              ∃ ci : Configuration, Configuration.step c1 ci ∧ Configuration.pathN n ci c2

-- Definition of Paths
-- This is the reduced definition of paths, without having to provide the length
-- "is there a path of which starts in a and ends in b, while a and b are configurations"
-- expressed differently: does (l,σ) →ᵏ (l',σ') hold, while k ∈ ℕ
def Configuration.path (c1 c2 : Configuration) : Prop :=
  ∃ n : Nat, Configuration.pathN n c1 c2


-- Defining set of execution lengths
def Configuration.all_succ_lengths (c1 : Configuration) : Set ℕ∞ :=
  {k : ℕ∞ | ∃ (n : ℕ) (c : Configuration), k = n ∧ Configuration.pathN n c1 c}

-- Defining rc: supremum of set of all lengths
-- rc(σ) = sup { k ∈ ℕ | (l₀, σ) →ᵏ (_, _)}
noncomputable def Configuration.rc (c1 : Configuration) : ℕ∞:=
  sSup (Configuration.all_succ_lengths c1)


-- Definition of a Path
-- This is doesn't include Configurations, just if there is a path, regardless of states and guards.
--def IntegerProgram.pathN : Nat → Nat → Nat → IntegerProgram → Prop
--  | 0, _, _, _ => false
  --| 1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2
--  | n+1, l1, l2, ip => (∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2)
--  ∨ (∃ t ∈ ip.edges, t.src = l1 ∧ IntegerProgram.pathN n t.tgt l2 ip)

-- TODO: more precise definition, but breaks some proofs, integrate later!
--def IntegerProgram.pathN : Nat → Nat → Nat → IntegerProgram → Prop
--  | 0, _, _, _ => false
--  | 1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2
--  | n+1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ IntegerProgram.pathN n t.tgt l2 ip

def IntegerProgram.pathN : Nat → Nat → Nat → IntegerProgram → Prop
  | 0, l1, l2, _ => l1 = l2
  | n+1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ IntegerProgram.pathN n t.tgt l2 ip



-- Definition of Locations which are seen in path
-- REMARKS: this could be undecidable, should not be used.
-- TODO: transform to be defined differently
def IntegerProgram.pathLocs : ∀ (n : ℕ) (l1 l2 : ℕ) (p : IntegerProgram),
    IntegerProgram.pathN n l1 l2 p → List ℕ
  | 0, _, _, _, _ => []
  | 1, l1, l2, _, _=> [l1, l2]
  | n+2, l1, l2, ip, h => by
    --let ⟨t, _, _, h_next⟩ := h
    --l1 :: IntegerProgram.pathLocs (n+1) t.tgt l2 ip h_next
    sorry

-- Definition of Path
-- this is analog to the reduced definition of Paths with Configurations
-- It definies paths along Integer Programs without regarding guards or states
-- Notice this will always be true for path x x ip, if x ∈ ip, even if there isn't any loop.
def IntegerProgram.path (l1 l2 : Nat) (ip : IntegerProgram) : Prop  :=
  ∃ n : Nat, IntegerProgram.pathN n l1 l2 ip

-- Definition of whether there is a cycle
-- similar to IntegerProgram.
def IntegerProgram.hasCycle (x : Nat) (ip : IntegerProgram) : Prop :=
  ∃ n : Nat, IntegerProgram.pathN (n+1) x x ip

-- Definition of an acyclic Integer Program
def IntegerProgram.acyclic (p : IntegerProgram) : Prop :=
  ∀ x ∈ p.locs, IntegerProgram.hasCycle x p


-- Example of an Integer Programs


-- Knoten l₀, l₂ (starting location: l₀)
-- Variables x₀, x₁
-- Transition #1 (l₀, (x₀ > 0 ∨ x₁ < 0), [η(x₀)= x₀-1, η(x₁) = x₀-x₁], l₂)
-- Transition #2 (l₂, (x₁ = 0), [η(x₁) = 1], l₂)
-- State x₀ := 1, x₁ := 0

def upd1_1 : Update :=
  {pv := 0, expr := Expr.sub (Expr.var 0) (Expr.lit 1)}
def upd1_2 : Update :=
  {pv := 1, expr := Expr.sub (Expr.var 0) (Expr.var 1)}

def trans_1 : Transition :=
  {src := 0,
   tgt := 2,
   guard := Constraint.or (
    Constraint.gt (Expr.var 0) (Expr.lit 0)) (Constraint.lt (Expr.var 1) (Expr.lit 0)),
   update := [upd1_1, upd1_2]}

def trans_2 : Transition :=
  {src := 2,
   tgt := 2,
   guard := Constraint.eq (Expr.var 0) (Expr.lit 0),
   update := [{pv := 1, expr := Expr.lit 1}]}

def example_program : IntegerProgram :=
  {locs := [0, 2],
   l₀ := 0,
   edges := [trans_1, trans_2],
   h_strt := by decide,
   h_locs := by decide,
   h_trans := by decide,
   h_incom := by decide}



-- def rank
-- lemma rank_decreases
-- path_length_le_rank
-- pfade als liste
-- topologie als baum -> n-1 kanten
-- 1. bachelorarbeit anmelden
-- 2. nächsten ziele
-- wenn das fertig machen, mit azyklisch
-- 1. tool kette, parser zum einlesen
-- 2. snt-solver (sat solver), smt solver
-- 3. variante als snt eigenschaft kodieren
-- 4. variante als template, zB schleife x>0,
-- 5. tool sind programme kreisfrei, wie macht man in lean einenNat parser.
-- 6. als tool ausführbar, programme einlesen und dann bestimmen was die korrektheit ist.
-- 7.
/-
def pathNodes :
    ∀ {n l1 l2 p}, IntegerProgram.pathN n l1 l2 p → List Nat
  | 0, _, _, _, h => by cases h
  | 1, l1, l2, p, h => [l1, l2]
  | n+2, l1, l2, p, h =>
      by
        dsimp [IntegerProgram.pathN] at h
        rcases h with
        | Or.inl h =>
            [l1, l2]
        | Or.inr h =>
            rcases h with ⟨t, _, rfl, hrec⟩
            l1 :: pathNodes hrec

lemma pathNodes_nodup
    (p : IntegerProgram)
    (hac : p.acyclic)
    {n l1 l2}
    (h : IntegerProgram.pathN n l1 l2 p) :
    (pathNodes h).Nodup := by
  -- Proof sketch:
  -- Induction on h
  -- If a node repeats,
  -- we extract a subpath l → l
  -- contradicting acyclicity
  induction h with
  | zero => cases h
  | succ _ _ _ =>
      simp [pathNodes]
  | step _ _ _ _ hstep ih =>
      simp [pathNodes]
      exact List.Nodup.cons ?hne ih
  -- The non-equality follows from acyclicity
  -- (details depend slightly on your exact path encoding)


theorem acyclic_implies_finite_run
    (p : IntegerProgram)
    (hac : p.acyclic)
    {n l1 l2}
    (h : IntegerProgram.pathN n l1 l2 p) :
    n ≤ p.locs.length := by
  have hnodup := pathNodes_nodup p hac h
  have hsubset :
      pathNodes h ⊆ p.locs := by
    -- easy induction on path
    admit
  have := List.length_le_of_nodup_of_subset hnodup hsubset
  -- length(pathNodes h) = n+1 or n depending on encoding
  -- conclude bound on n
  admit
-/
-/
