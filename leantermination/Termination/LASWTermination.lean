import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Ring.Defs


namespace LASW

/--
 `n` is the number of program variables.
 `m` is the number of inequalities in the matrix encoding `(A A')(x, x') ≤ b`.
 `A`, `A'` are `m × n` matrices over `ℚ`.
 `b : Fin m → ℚ` is the right-hand side vector.
 `lambda₁`, `lambda₂` are nonnegative *row* vectors of length `m`.
-/
structure FarkasWitness (n m : ℕ) where
  A : Fin m → Fin n → ℚ
  A' : Fin m → Fin n → ℚ
  b  : Fin m → ℚ
  lambda₁ : Fin m → ℚ
  lambda₂ : Fin m → ℚ
  h_nonneg₁ : ∀ i, 0 ≤ lambda₁ i
  h_nonneg₂ : ∀ i, 0 ≤ lambda₂ i
  -- (1a)  λ₁ · A' = 0   (as a row vector of length n)
  h_1a : ∀ j : Fin n, ∑ i, lambda₁ i * A' i j = 0
  -- (1b)  (λ₁ - λ₂) · A = 0
  h_1b : ∀ j : Fin n, ∑ i, (lambda₁ i - lambda₂ i) * A i j = 0
  -- (1c)  λ₂ · (A + A') = 0
  h_1c : ∀ j : Fin n, ∑ i, lambda₂ i * (A i j + A' i j) = 0
  -- (1d)  λ₂ · b < 0
  h_1d : ∑ i, lambda₂ i * b i < 0

namespace FarkasWitness

variable {n m : ℕ} (w : FarkasWitness n m)

/-- Coefficients of the linear ranking function:  `r := λ₂ · A'`. -/
def r (j : Fin n) : ℚ := ∑ i, w.lambda₂ i * w.A' i j

/-- Lower bound constant:  `δ₀ := -(λ₁ · b)`. -/
def delta₀ : ℚ := -(∑ i, w.lambda₁ i * w.b i)

/-- Strict decrease amount:  `δ := -(λ₂ · b)`. Positive by (1d). -/
def delta : ℚ := -(∑ i, w.lambda₂ i * w.b i)

/-- `δ > 0`, immediately from condition (1d). -/
lemma delta_pos : 0 < w.delta := by
  unfold delta
  exact neg_pos.mpr w.h_1d
  -- TODO: unfold `delta`; use `h_1d`; `linarith`.


end FarkasWitness


/--
Convert an `Env` (a `List Int`) into a rational vector of length `n`.
Indices past the list default to 0.
-/
def Env.toVec (n : ℕ) (env : Env) : Fin n → ℚ :=
  fun i => (env.vars[i.val]?).map (fun z => (z : ℚ)) |>.getD 0

/--
A single semantic step: there is an edge `t` of `ip` such that its guard
holds at `env` and its update yields `env'`. Extracted from `SemanticPath.cons`
for cleaner reasoning.
-/
def SemanticStep (ip : IntegerProgram) (env env' : Env) : Prop :=
  ∃ t ∈ ip.edges,
    Constraint.eval t.guard env = some true ∧
    Update.all t.update env = some env'

/--
Encoding correctness for a single transition: whenever `t` performs a step
from `env` to `env'`, the matrix inequality `(A A')(env, env')ᵀ ≤ b` holds.

-/
def FarkasWitness.RepresentsTransition
    {n m : ℕ} (w : FarkasWitness n m) (t : Transition) : Prop :=
  ∀ env env' : Env,
    Constraint.eval t.guard env = some true →
    Update.all t.update env = some env' →
    ∀ i : Fin m,
      (∑ j, w.A i j * Env.toVec n env j) +
      (∑ j, w.A' i j * Env.toVec n env' j) ≤ w.b i

/-- For a whole program: the witness must represent every edge. -/
def FarkasWitness.RepresentsProgram
    {n m : ℕ} (w : FarkasWitness n m) (ip : IntegerProgram) : Prop :=
  ∀ t ∈ ip.edges, w.RepresentsTransition t

/--
A single semantic step implies the matrix inequality.

-/
lemma step_implies_matrix
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    ∀ i : Fin m,
      (∑ j, w.A i j * Env.toVec n env j) +
      (∑ j, w.A' i j * Env.toVec n env' j) ≤ w.b i := by
  -- Unpack h_step: get the transition t, the fact it's an edge,
  -- the guard, and the update.
  obtain ⟨t, h_edge, hguard, hupdate⟩ := h_step
  -- h_repr applied to t gives us RepresentsTransition for that specific t.
  have h_repr_t : w.RepresentsTransition t := h_repr t h_edge
  -- RepresentsTransition is itself a ∀-statement; apply it.
  intro i
  exact h_repr_t env env' hguard hupdate i


/--
Decrease Lemma

The linear function `r · x` strictly decreases by at least `δ` on every step:
  `r · env' ≤ r · env - δ`.
-/
lemma decrease_on_step
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    (∑ j, w.r j * Env.toVec n env' j) ≤
    (∑ j, w.r j * Env.toVec n env j) - w.delta := by
  set x  : Fin n → ℚ := Env.toVec n env  with hx
  set x' : Fin n → ℚ := Env.toVec n env' with hx'

  have h_mat : ∀ i : Fin m,
      (∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j) ≤ w.b i :=
    step_implies_matrix h_repr h_step

  -- Multiply row i by λ₂(i) ≥ 0 and sum.
  have h_sum :
      (∑ i, w.lambda₂ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      ≤ ∑ i, w.lambda₂ i * w.b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h_mat i) (w.h_nonneg₂ i)

  -- distribute λ₂(i) over the inner addition:
  have h_dist : ∀ i,
      w.lambda₂ i * ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j))
      = (∑ j, w.lambda₂ i * (w.A i j * x j))
      + (∑ j, w.lambda₂ i * (w.A' i j * x' j)) := by
    intro i
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]

  -- Apply h_dist termwise and split the outer sum
  have h_lhs_eq :
      (∑ i, w.lambda₂ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      = (∑ i, ∑ j, w.lambda₂ i * (w.A  i j * x  j))
      + (∑ i, ∑ j, w.lambda₂ i * (w.A' i j * x' j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_dist i

  -- Swap the order of summation in each double sum
  have h_swap_A :
      (∑ i, ∑ j, w.lambda₂ i * (w.A i j * x j))
      = ∑ j, (∑ i, w.lambda₂ i * w.A i j) * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have h_swap_A' :
      (∑ i, ∑ j, w.lambda₂ i * (w.A' i j * x' j))
      = ∑ j, (∑ i, w.lambda₂ i * w.A' i j) * x' j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

  -- λ₂ A' = r by definition of r
  have h_lam2A' : ∀ j, (∑ i, w.lambda₂ i * w.A' i j) = w.r j := by
    intro j; rfl  -- w.r is defined as exactly this sum

  -- λ₂ A = -r, derived from h_1c
  -- h_1c says: ∀ j, ∑ i, λ₂ i * (A i j + A' i j) = 0
  -- which means: (λ₂ A)(j) + (λ₂ A')(j) = 0
  -- hence:        (λ₂ A)(j) = -(λ₂ A')(j) = -r(j).
  have h_lam2A : ∀ j, (∑ i, w.lambda₂ i * w.A i j) = -w.r j := by
    intro j
    have := w.h_1c j
    -- this : ∑ i, λ₂ i * (A i j + A' i j) = 0
    -- split the inner mul-add
    have h_split :
        (∑ i, w.lambda₂ i * (w.A i j + w.A' i j))
        = (∑ i, w.lambda₂ i * w.A i j) + (∑ i, w.lambda₂ i * w.A' i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_split, h_lam2A' j] at this
    linarith

  -- Apply the two identifications to rewrite both sums
  have h_lhs_final :
    (∑ i, w.lambda₂ i *
      ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
    = (∑ j, (-w.r j) * x j) + (∑ j, w.r j * x' j) := by
    rw [h_lhs_eq, h_swap_A, h_swap_A']
  -- After this, the goal should be:
  --   (∑ j, (∑ i, λ₂ i * A i j) * x j) + (∑ j, (∑ i, λ₂ i * A' i j) * x' j)
  --   = (∑ j, (-w.r j) * x j) + (∑ j, w.r j * x' j)
  -- Rewrite each inner sum using h_lam2A and h_lam2A':
    simp_rw [h_lam2A, h_lam2A']

  -- ---- Step 5: rearrange to the goal ----
  -- We now have:
  --   (∑ j, -r j * x j) + (∑ j, r j * x' j) ≤ ∑ i, λ₂ i * b i
  -- The RHS equals -δ by definition of δ.
  -- Rearranging: ∑ r j * x' j ≤ ∑ r j * x j - δ.

  -- λ₂·b = -δ
  have h_rhs : (∑ i, w.lambda₂ i * w.b i) = -w.delta := by
    show _ = -(-(∑ i, w.lambda₂ i * w.b i))
    ring

  -- Pull the minus sign out of the first sum on the LHS
  have h_neg_sum : (∑ j, (-w.r j) * x j) = -(∑ j, w.r j * x j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

  -- Put h_sum, h_lhs_final, h_rhs, h_neg_sum together
  rw [h_lhs_final] at h_sum
  rw [h_neg_sum, h_rhs] at h_sum
  -- h_sum is now:  -(∑ r j * x j) + (∑ r j * x' j) ≤ -δ
  linarith
   -- TODO: follow the 5-step outline.
        -- Key Mathlib lemmas to know:
        --   * `Finset.mul_sum`, `Finset.sum_mul` (distributing)
        --   * `Finset.sum_le_sum` (componentwise ≤ to sums)
        --   * `mul_nonneg` (for `λ₂ i ≥ 0`)

/--
Any loop-eligible state `env` (one that admits a successor) satisfies
`r · env ≥ δ₀`.
-/
lemma bounded_on_loop_state
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    (env : Env) (h_loop : ∃ env', SemanticStep ip env env') :
    w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j := by

  obtain ⟨env', h_step⟩ := h_loop
  set x  : Fin n → ℚ := Env.toVec n env  with hx
  set x' : Fin n → ℚ := Env.toVec n env' with hx'
    -- ---- Step 1: matrix inequality on every row ----
  have h_mat : ∀ i : Fin m,
      (∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j) ≤ w.b i :=
    step_implies_matrix h_repr h_step

  -- ---- Step 2: nonneg-weighted sum over rows ----
  -- Multiply row i by λ₁(i) ≥ 0 and sum.
  have h_sum :
      (∑ i, w.lambda₁ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      ≤ ∑ i, w.lambda₁ i * w.b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h_mat i) (w.h_nonneg₁ i)

  -- expand λ₁
  have h_dist : ∀ i,
      w.lambda₁ i * ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j))
      = (∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ j, w.lambda₁ i * (w.A' i j * x' j)) := by
    intro i
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]

  have h_lhs_eq :
      (∑ i, w.lambda₁ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      = (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_dist i

  have h_expand :
      (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) ≤ ∑ i, w.lambda₁ i * w.b i := by
      simpa [h_lhs_eq] using h_sum

  -- apply that 1a
  have h_swap_A :
      (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      = ∑ j, (∑ i, w.lambda₁ i * w.A i j) * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have h_swap_A' :
      (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j))
      = ∑ j, (∑ i, w.lambda₁ i * w.A' i j) * x' j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

  have h_zero :
      (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      ≤ ∑ i, w.lambda₁ i * w.b i := by
    -- The A'-double-sum vanishes because of (1a).
    have hp : (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) = 0 := by
      rw [h_swap_A']
      -- goal: ∑ j, (∑ i, λ₁ i * A' i j) * x' j = 0
      apply Finset.sum_eq_zero
      intro j _
      rw [w.h_1a j, zero_mul]
    rw [hp, add_zero] at h_expand
    exact h_expand

  -- a λ₁A = λ₂A
  -- (1b): λ₁ A = λ₂ A   (column-wise)
  have h_eq : ∀ j, (∑ i, w.lambda₁ i * w.A i j) = (∑ i, w.lambda₂ i * w.A i j) := by
    intro j
    have h := w.h_1b j
    -- h : ∑ i, (λ₁ i - λ₂ i) * A i j = 0
    have h_split :
        (∑ i, (w.lambda₁ i - w.lambda₂ i) * w.A i j)
        = (∑ i, w.lambda₁ i * w.A i j) - (∑ i, w.lambda₂ i * w.A i j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_split] at h
    linarith

  -- (1c): λ₂ A = -r   (column-wise)
  have h_lam2A : ∀ j, (∑ i, w.lambda₂ i * w.A i j) = -w.r j := by
    intro j
    have hc := w.h_1c j
    -- hc : ∑ i, λ₂ i * (A i j + A' i j) = 0
    have hc_split :
        (∑ i, w.lambda₂ i * (w.A i j + w.A' i j))
        = (∑ i, w.lambda₂ i * w.A i j) + (∑ i, w.lambda₂ i * w.A' i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    -- ∑ i, λ₂ i * A' i j = r j  (by definition of r)
    have h_lam2A' : (∑ i, w.lambda₂ i * w.A' i j) = w.r j := rfl
    rw [hc_split, h_lam2A'] at hc
    linarith
  -- Combine: λ₁ A = -r  (column-wise)
  have h_lam1A : ∀ j, (∑ i, w.lambda₁ i * w.A i j) = -w.r j := by
    intro j
    rw [h_eq j, h_lam2A j]
  -- Rewrite h_zero's LHS using the swap, then identify the inner sum with -r.
  -- h_zero : ∑ i, ∑ j, λ₁ i * (A i j * x j) ≤ ∑ i, λ₁ i * b i
  rw [h_swap_A] at h_zero
  -- h_zero : ∑ j, (∑ i, λ₁ i * A i j) * x j ≤ ∑ i, λ₁ i * b i

  -- Replace each inner column sum with -r j.
  have h_lhs_r : (∑ j, (∑ i, w.lambda₁ i * w.A i j) * x j)
               = ∑ j, (-w.r j) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [h_lam1A j]
  rw [h_lhs_r] at h_zero
  -- h_zero : ∑ j, (-r j) * x j ≤ ∑ i, λ₁ i * b i

  -- Pull the minus sign out of the LHS sum.
  have h_neg : (∑ j, (-w.r j) * x j) = -(∑ j, w.r j * x j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_neg] at h_zero
  -- h_zero : -(∑ j, r j * x j) ≤ ∑ i, λ₁ i * b i

  -- The RHS is -δ₀ by definition of δ₀.
  have h_rhs : (∑ i, w.lambda₁ i * w.b i) = -w.delta₀ := by
    unfold FarkasWitness.delta₀
    ring
  rw [h_rhs] at h_zero
  -- h_zero : -(∑ j, r j * x j) ≤ -δ₀

  -- Goal: δ₀ ≤ ∑ j, r j * x j.  This follows by linarith.
  linarith


/--
The ranking function ρ from the paper
-/
noncomputable def FarkasWitness.rho
    {n m : ℕ} (w : FarkasWitness n m) (ip : IntegerProgram) (env : Env) : ℚ :=
  letI : Decidable (∃ env', SemanticStep ip env env') := Classical.propDecidable _
  if (∃ env', SemanticStep ip env env') then
    ∑ j, w.r j * Env.toVec n env j
  else
    w.delta₀ - w.delta

/-
ρ strictly decreases by `δ` on every step.
-/
lemma rho_strict_decrease
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    w.rho ip env' ≤ w.rho ip env - w.delta := by
  -- env is loop-eligible: h_step witnesses a successor.
  have h_env_loop : ∃ e', SemanticStep ip env e' := ⟨env', h_step⟩
  -- Unfold ρ at both env and env'.
  unfold FarkasWitness.rho
  -- ρ(env) reduces to r·env since env is loop-eligible.
  rw [if_pos h_env_loop]
  -- Now case-split on whether env' is loop-eligible.
  by_cases h_env'_loop : ∃ e'', SemanticStep ip env' e''
  · -- Case 1: env' loop-eligible → ρ(env') = r·env'.
    rw [if_pos h_env'_loop]
    -- Goal: ∑ j, r j * (toVec env') ≤ (∑ j, r j * (toVec env)) - δ
    exact decrease_on_step h_repr h_step
  · -- Case 2: env' NOT loop-eligible → ρ(env') = δ₀ - δ.
    rw [if_neg h_env'_loop]
    -- Goal: δ₀ - δ ≤ (∑ j, r j * (toVec env)) - δ
    -- Suffices: δ₀ ≤ ∑ j, r j * (toVec env), which is bounded_on_loop_state.
    have h_bound : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j :=
      bounded_on_loop_state h_repr env h_env_loop
    linarith

/--
ρ is bounded below by `δ₀ - δ` on every state.
-/
lemma rho_lower_bound
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    (env : Env) :
    w.delta₀ - w.delta ≤ w.rho ip env := by
  unfold FarkasWitness.rho
  by_cases h_env: ∃ e', SemanticStep ip env e'
  · -- Case eligable
    rw [if_pos h_env]
    have h_bound : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j :=
      bounded_on_loop_state h_repr env h_env
    have h_mec : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j + w.delta :=
      le_trans h_bound (le_add_of_nonneg_right (le_of_lt w.delta_pos))
    simpa
  · -- trivial case
    rw [if_neg h_env]


/--
This lemma is reusable for any ranking-function-based termination method.
-/
lemma path_length_bounded_by_ranking
    (ip : IntegerProgram)
    (ρ : Env → ℚ) (L δ : ℚ) (hδ : 0 < δ)
    (h_bound : ∀ env, L ≤ ρ env)
    (h_decrease : ∀ env env', SemanticStep ip env env' → ρ env' ≤ ρ env - δ)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    (p.length : ℚ) * δ ≤ ρ env - L := by
  induction p with
  | nil u env h =>
    simp only [SemanticPath.length, Nat.cast_zero, zero_mul, sub_nonneg]
    exact h_bound env
  | cons env t h_edge hguard env' hupdate p' ih =>
      have h_step : SemanticStep ip env env' :=
        ⟨t, h_edge, hguard, hupdate⟩
      have h_dec : ρ env' ≤ ρ env - δ := h_decrease env env' h_step
      -- ih : (p'.length : ℚ) * δ ≤ ρ env' - L
      simp only [SemanticPath.length, Nat.cast_add, Nat.cast_one, ge_iff_le]
      -- goal: (1 + p'.length) * δ ≤ ρ env - L  (after Nat.cast push)
      -- ring/linarith time
      have : ((1 + p'.length : ℕ) : ℚ) * δ = δ + (p'.length : ℚ) * δ := by push_cast; ring
      linarith [ih, h_dec]

/--
the path length as a natural number is bounded.
-/
lemma path_length_le_bound
    (ip : IntegerProgram)
    (ρ : Env → ℚ) (L δ : ℚ) (hδ : 0 < δ)
    (h_bound : ∀ env, L ≤ ρ env)
    (h_decrease : ∀ env env', SemanticStep ip env env' → ρ env' ≤ ρ env - δ)
    (env : Env) :
    ∃ N : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v), p.length ≤ N := by
      -- Pick N := ⌈(ρ env - L) / δ⌉₊
  refine ⟨⌈(ρ env - L) / δ⌉₊, ?_⟩
  intro u v p
  -- Get the raw rational bound
  have h_raw : (p.length : ℚ) * δ ≤ ρ env - L :=
    path_length_bounded_by_ranking ip ρ L δ hδ h_bound h_decrease p
  -- Divide by δ > 0
  have h_div : (p.length : ℚ) ≤ (ρ env - L) / δ := by
    rw [le_div_iff₀ hδ]
    exact h_raw
  -- Cast through Nat.ceil
  have : (p.length : ℚ) ≤ (⌈(ρ env - L) / δ⌉₊ : ℚ) :=
    le_trans h_div (Nat.le_ceil _)
  exact_mod_cast this




/--
If a Farkas witness `w` represents `ip`, then `ip` terminates.
-/
theorem termination_of_farkas_witness
    {n m : ℕ} {ip : IntegerProgram}
    (w : FarkasWitness n m) (h_repr : w.RepresentsProgram ip) :
    ip.Termination := by
  intro env
  -- Apply Layer 5 with ρ := w.rho ip, L := δ₀ - δ, δ := w.delta.
  exact path_length_le_bound ip (w.rho ip) (w.delta₀ - w.delta) w.delta
    w.delta_pos
    (rho_lower_bound h_repr)
    (fun _ _ h => rho_strict_decrease h_repr h)
    env


end LASW
