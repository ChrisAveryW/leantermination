import leantermination.Datastructures.IntegerProgram
import leantermination.Termination.LASWTermination
import Mathlib.Tactic

open LASW

/-
  Termination for programs that are ACYCLIC UP TO SELF-LOOPS
  ==========================================================

  Strategy ("Approach A" — direct, single path world):

  A run of the program alternates between
    * SELF-LOOP steps   (edges with t.src = t.tgt), bounded per location by a
                         Farkas witness via a ranking function, and
    * SKELETON steps     (edges with t.src ≠ t.tgt), bounded in number by
                         acyclicity of the skeleton graph.

  Total path length = (self-loop steps) + (skeleton steps), each bounded.

  Pipeline (bottom-up build order):

    Layer A1 : SemanticPath.usesOnly / step counters         -- predicates & measures on paths
    Layer A2 : selfloop_run_bounded                          -- a single self-loop run is bounded
                                                                (reuses LASW Layer 3/4/5)
    Layer A3 : skeleton_path_bounded                          -- skeleton paths bounded by acyclicity
                                                                (pure graph theory, no Farkas)
    Layer A4 : path_length_decompose                          -- length = selfloop steps + skeleton steps
    Layer A5 : terminates_of_selfloops_rank                   -- MAIN THEOREM (composition)

  Suggested implementation order: A1 → A2 → A3 → A4 → A5.
  Start with A2 (it de-risks the whole approach); A1 is just definitions it needs.

  NOTE: `transition_to_ip` is NOT needed in this approach and can be deleted.
-/

namespace IntegerProgram

/-! ## Skeleton definitions (graph structure) -/

/-- The self-loop edges of `ip` (those with equal source and target). -/
def selfLoops (ip : IntegerProgram) : List Transition :=
  ip.edges.filter (fun t => t.src = t.tgt)

/-- The program with self-loops removed: the "skeleton". -/
def withoutSelfLoops (ip : IntegerProgram) : IntegerProgram :=
  { locs   := ip.locs
  , l₀     := ip.l₀
  , edges  := ip.edges.filter (fun t => t ∉ ip.selfLoops)
  , h_edges := by
      intro t ht
      simp only [decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at ht
      exact ip.h_edges t ht.1 }

/-- `ip` is acyclic once self-loops are removed. -/
def AcyclicUpToSelfLoops (ip : IntegerProgram) : Prop :=
  IntegerProgram.Acyclic ip.withoutSelfLoops

/-- A transition is a self-loop iff its source and target coincide. -/
def Transition.isSelfLoop (t : Transition) : Prop := t.src = t.tgt

instance (t : Transition) : Decidable t.isSelfLoop := by
  unfold Transition.isSelfLoop; infer_instance

end IntegerProgram


/-! ## Layer A1: Predicates and step counters on paths -/

namespace SemanticPath

/--
`p.usesOnly t` holds when every step of the path fires transition `t`.
Used to characterize "a pure self-loop run at one location".
-/
def usesOnly {ip : IntegerProgram} (t : Transition) :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Prop
  | _, _, _, .nil _ _ _          => True
  | _, _, _, .cons _ t' _ _ _ _ p => t' = t ∧ usesOnly t p

/-- Number of self-loop steps (edges with `src = tgt`) along the path. -/
def selfLoopSteps {ip : IntegerProgram} :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Nat
  | _, _, _, .nil _ _ _          => 0
  | _, _, _, .cons _ t _ _ _ _ p =>
      (if t.src = t.tgt then 1 else 0) + selfLoopSteps p

/-- Number of skeleton steps (edges with `src ≠ tgt`) along the path. -/
def skeletonSteps {ip : IntegerProgram} :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Nat
  | _, _, _, .nil _ _ _          => 0
  | _, _, _, .cons _ t _ _ _ _ p =>
      (if t.src = t.tgt then 0 else 1) + skeletonSteps p

end SemanticPath


/-! ## Layer A2: A single self-loop run is bounded -/

/--
**Self-loop bound.**

If a path uses only the self-loop transition `t`, and `t` has a Farkas witness,
then the path length is bounded.

This reuses the LASW Layer 5 machinery: a `usesOnly t` path consists only of
`t`-steps, and `w.rho` decreases by `δ` on every `t`-step (Layer 4) and is
bounded below (Layer 4). So `path_length_bounded_by_ranking` applies.

NOTE: This is the riskiest assumption of the whole approach — prove it FIRST.

PROOF OUTLINE:
  * `w.rho ip` is bounded below by `δ₀ - δ`  (rho_lower_bound)
  * `w.rho ip` decreases by `δ` on every t-step  (rho_strict_decrease, since the
    step is a SemanticStep)
  * Apply path_length_le_bound (or path_length_bounded_by_ranking) to get a bound.

  The `usesOnly t` hypothesis may not even be needed if the witness's ρ decreases
  on EVERY step of ip (which it does, since rho_strict_decrease works for any
  SemanticStep). If your witness only represents `t`, you DO need usesOnly so that
  every step is a t-step and h_repr applies. Decide based on whether `h_repr`
  covers all of ip or just t.
-/
lemma selfloop_run_bounded
    {ip : IntegerProgram} {t : Transition}
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges)
    {n m : ℕ} (w : FarkasWitness n m)
    (h_repr : w.RepresentsProgram ip)
    (env : Env) :
    ∃ N : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v), p.length ≤ N := by
  -- This is essentially `termination_of_farkas_witness` specialized: a single
  -- witness representing all of `ip` already bounds every path.
  -- (If `h_repr` only represents `t`, restrict via `usesOnly t` and a variant.)
  exact path_length_le_bound ip (w.rho ip) (w.delta₀ - w.delta) w.delta
    w.delta_pos
    (rho_lower_bound h_repr)
    (fun _ _ h => rho_strict_decrease h_repr h)
    env
  -- TODO: if you instead have a per-location witness that only represents the
  -- single self-loop, you'll want a `usesOnly t`-restricted version. See note.


/-! ## Layer A3: Skeleton paths bounded by acyclicity (pure graph theory) -/

/--
**Skeleton bound.**

In a graph that is acyclic after removing self-loops, any path that takes only
skeleton steps (never repeats a location) has length bounded by the number of
locations.

This has NO Farkas content. It's the graph-theoretic fact: a simple path in a
DAG with `L` nodes has at most `L - 1` edges.

PROOF OUTLINE (mirrors your commented-out `acyclic_implies_finite_run`):
  * A skeleton path visits a sequence of locations.
  * By acyclicity (no cycles in the skeleton), no location repeats.
  * Hence the number of distinct locations ≥ path length, bounded by ip.locs.length.

You likely need a helper that extracts the list of visited locations from a path
and proves it has no duplicates (Nodup) under acyclicity, then bounds its length
by `ip.locs.length` via `List.Nodup.length_le_of_subset` or similar.
-/
lemma skeleton_steps_bounded
    {ip : IntegerProgram} (h_upto : ip.AcyclicUpToSelfLoops)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.skeletonSteps ≤ ip.locs.length := by
  sorry
  -- TODO: pure graph theory. Extract visited locations, show Nodup via
  --       h_upto (acyclicity of the skeleton), bound by ip.locs.length.


/-! ## Layer A4: Length decomposition -/

/--
**Decomposition.**

Every path's length equals the number of self-loop steps plus the number of
skeleton steps. Immediate by induction on the path (each step is exactly one or
the other, by case analysis on `t.src = t.tgt`).
-/
lemma length_eq_selfloop_add_skeleton
    {ip : IntegerProgram} {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.length = p.selfLoopSteps + p.skeletonSteps := by
  induction p with
  | nil u env h =>
      simp [SemanticPath.length, SemanticPath.selfLoopSteps, SemanticPath.skeletonSteps]
  | cons env t h_edge hguard env' hupdate p' ih =>
      simp only [SemanticPath.length, SemanticPath.selfLoopSteps,
                 SemanticPath.skeletonSteps]
      -- goal: 1 + p'.length
      --     = ((if t.src=t.tgt then 1 else 0) + p'.selfLoopSteps)
      --     + ((if t.src=t.tgt then 0 else 1) + p'.skeletonSteps)
      split_ifs with h
      · -- self-loop step
        omega
      · -- skeleton step
        omega
  -- TODO: if `omega` doesn't close it directly, rewrite `ih` first:
  --   rw [ih]; split_ifs <;> ring


/-! ## Layer A5: The Main Theorem -/

/--
**Main theorem: termination of programs acyclic up to self-loops.**

If the skeleton (self-loops removed) is acyclic, and every self-loop has a
Farkas-witnessed ranking function, the program terminates.

PROOF STRATEGY:
  Given an arbitrary path `p`, decompose its length:
    p.length = selfLoopSteps + skeletonSteps           (length_eq_selfloop_add_skeleton)
  Bound each part:
    skeletonSteps ≤ ip.locs.length                     (skeleton_steps_bounded)
    selfLoopSteps ≤ (some bound from the witnesses)     (from selfloop_run_bounded,
                                                          summed/maxed over locations)
  Add the two bounds for a uniform N.

  The self-loop part is the subtle bit: a path may enter and leave a self-loop
  many times (interleaved with skeleton steps). You need to bound the TOTAL
  self-loop steps, which means: at most (number of locations) visits, each visit
  contributing at most (that location's self-loop bound) steps. So
    selfLoopSteps ≤ (number of skeleton segments + 1) * (max self-loop bound)
                  ≤ (ip.locs.length + 1) * B
  where B is the max over self-loops of their individual bounds.

  This requires a lemma bounding the self-loop steps of any single "burst"
  (maximal run of one self-loop t) via selfloop_run_bounded, then multiplying by
  the number of bursts (bounded by skeleton structure).
-/
theorem terminates_of_selfloops_rank
    {ip : IntegerProgram}
    (h_witnesses : ∀ t ∈ ip.selfLoops,
        ∃ (n m : ℕ) (w : FarkasWitness n m),
          w.RepresentsProgram ip)   -- or: represents just the self-loop t
    (h_upto : ip.AcyclicUpToSelfLoops) :
    ip.Termination := by
  intro env
  sorry
  -- TODO: assemble.
  --  1. From h_upto + skeleton_steps_bounded: skeletonSteps ≤ ip.locs.length.
  --  2. From h_witnesses + selfloop_run_bounded: each self-loop burst is bounded;
  --     bound the total self-loop steps.
  --  3. From length_eq_selfloop_add_skeleton: p.length = sum of the two.
  --  4. Provide N := (self-loop total bound) + ip.locs.length and discharge.


/-! ## Helper lemmas you will likely need along the way -/

/--
A single maximal self-loop burst at a location is bounded.
Bridges `usesOnly t` paths to `selfloop_run_bounded`.
-/
lemma selfloop_burst_bounded
    {ip : IntegerProgram} {t : Transition}
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges)
    {n m : ℕ} (w : FarkasWitness n m) (h_repr : w.RepresentsProgram ip)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v)
    (h_uses : p.usesOnly t) :
    ∃ N : Nat, p.length ≤ N := by
  sorry
  -- TODO: follows from selfloop_run_bounded; the `usesOnly t` hypothesis ensures
  --       every step is a t-step so h_repr applies cleanly.

/--
The total number of self-loop steps in any path is bounded:
at most (skeleton segments + 1) times the maximum per-burst bound.
-/
lemma total_selfloop_steps_bounded
    {ip : IntegerProgram}
    (h_witnesses : ∀ t ∈ ip.selfLoops,
        ∃ (n m : ℕ) (w : FarkasWitness n m), w.RepresentsProgram ip)
    (h_upto : ip.AcyclicUpToSelfLoops)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    ∃ B : Nat, p.selfLoopSteps ≤ B := by
  sorry
  -- TODO: the genuinely hard composition step. Bound the number of self-loop
  --       bursts by the skeleton structure, each burst by selfloop_burst_bounded.

end -- (close any open section/namespace as needed)
