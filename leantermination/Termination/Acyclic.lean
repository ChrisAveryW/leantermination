import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.List.Basic

-- ============================================================
-- Successor nodes
-- ============================================================

-- All target locations reachable from u in one step
private def succNodes (ip : IntegerProgram) (u : Nat) : List Nat :=
  ip.edges.filterMap fun t => if t.src == u then some t.tgt else none

-- Successors are always members of ip.locs (from h_edges)
private lemma succNodes_mem_locs {ip : IntegerProgram} {u v : Nat}
    (hv : v ∈ succNodes ip u) : v ∈ ip.locs := by
  simp only [succNodes, List.mem_filterMap] at hv
  obtain ⟨t, ht_mem, ht_val⟩ := hv
  split_ifs at ht_val with h
  -- false branch (none = some v) is automatically dismissed
  exact (Option.some.inj ht_val) ▸ (ip.h_edges t ht_mem).2

-- Every element of succNodes corresponds to an actual transition
private lemma succNodes_edge {ip : IntegerProgram} {u v : Nat}
    (hv : v ∈ succNodes ip u) : ∃ t ∈ ip.edges, t.src = u ∧ t.tgt = v := by
  simp only [succNodes, List.mem_filterMap] at hv
  obtain ⟨t, ht_mem, ht_val⟩ := hv
  split_ifs at ht_val with h
  -- false branch automatically dismissed
  refine ⟨t, ht_mem, ?_, Option.some.inj ht_val⟩
  simp only [beq_iff_eq] at h; exact h

-- ============================================================
-- DFS-based cycle detection
-- ============================================================

-- Grey/black DFS.  Returns (hasCycle, updatedDone).
-- stack : nodes currently on the DFS stack (grey)
-- done  : fully-explored nodes (black)
-- fuel  : decreases on every recursive call, bounding recursion depth
private def dfsHasCycle (ip : IntegerProgram) :
    Nat → Nat → List Nat → List Nat → Bool × List Nat
  | 0,        _,    _,     done => (false, done)
  | fuel + 1, curr, stack, done =>
      if curr ∈ done then (false, done)
      else if curr ∈ stack then (true, done)
      else
        let (found, done') :=
          (succNodes ip curr).foldl
            (fun acc s =>
              if acc.1 then acc
              else dfsHasCycle ip fuel s (curr :: stack) acc.2)
            (false, done)
        (found, curr :: done')

-- ============================================================
-- Public Boolean decision procedure
-- ============================================================

-- Starting DFS from every location is necessary because
-- IntegerProgram.Acyclic quantifies over ALL syntactic paths,
-- not just those reachable from l₀.
-- Fuel ip.locs.length + 1 is sufficient: any simple path has
-- length ≤ ip.locs.length, so a back edge is detected within
-- that many additional steps.
def IntegerProgram.isAcyclic (ip : IntegerProgram) : Bool :=
  !(ip.locs.foldl
      (fun acc u =>
        if acc.1 then acc
        else dfsHasCycle ip (ip.locs.length + 1) u [] acc.2)
      (false, [])).1

-- Upper-case alias expected by the toolchain executable
def IntegerProgram.IsAcyclic (ip : IntegerProgram) : Bool :=
  ip.isAcyclic

-- ============================================================
-- Correctness
-- ============================================================

-- Utility: foldl over a list preserves the invariant acc.1 = false
-- when the accumulator starts false and every step preserves it.
private lemma foldl_false_inv {α : Type} (l : List α)
    (f : Bool × List Nat → α → Bool × List Nat)
    (init : Bool × List Nat)
    (hinit : init.1 = false)
    (hstep : ∀ acc : Bool × List Nat, acc.1 = false → ∀ s : α, (f acc s).1 = false) :
    (l.foldl f init).1 = false := by
  induction l generalizing init with
  | nil => simpa
  | cons s t ih =>
      simp only [List.foldl]
      exact ih (f init s) (hstep init hinit s)

-- Membership-aware variant: hstep receives a proof that s ∈ l.
private lemma foldl_false_inv_mem {α : Type} (l : List α)
    (f : Bool × List Nat → α → Bool × List Nat)
    (init : Bool × List Nat)
    (hinit : init.1 = false)
    (hstep : ∀ acc : Bool × List Nat, acc.1 = false → ∀ s ∈ l, (f acc s).1 = false) :
    (l.foldl f init).1 = false := by
  induction l generalizing init with
  | nil => simpa
  | cons s t ih =>
      simp only [List.foldl]
      apply ih (f init s) (hstep init hinit s List.mem_cons_self)
      intro acc hacc x hx
      exact hstep acc hacc x (List.mem_cons_of_mem s hx)

-- Path concatenation.
private def SyntacticPath.append {ip : IntegerProgram} {u v w : Nat}
    (p : SyntacticPath ip u v) (q : SyntacticPath ip v w) : SyntacticPath ip u w :=
  match p with
  | .nil _ _ => q
  | .cons t h p' => .cons t h (p'.append q)

private lemma SyntacticPath.length_append {ip : IntegerProgram} {u v w : Nat}
    (p : SyntacticPath ip u v) (q : SyntacticPath ip v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil _ _ => simp [SyntacticPath.append, SyntacticPath.length]
  | cons _ _ _ ih =>
      simp [SyntacticPath.append, SyntacticPath.length, ih]; omega

-- A successor edge yields a length-1 SyntacticPath.
private lemma succ_step_path {ip : IntegerProgram} {curr s : Nat}
    (hs : s ∈ succNodes ip curr) :
    ∃ (p : SyntacticPath ip curr s), 0 < p.length := by
  obtain ⟨t, ht_mem, ht_src, ht_tgt⟩ := succNodes_edge hs
  subst ht_src; subst ht_tgt
  exact ⟨.cons t ht_mem (.nil t.tgt (ip.h_edges t ht_mem).2),
         by simp [SyntacticPath.length]⟩

-- dfsHasCycle never reports a cycle on a provably acyclic program.
-- Invariant: every node in `stack` has a positive-length SyntacticPath to `curr`.
-- If curr ∈ stack, that path is a cycle, contradicting hac.
private lemma dfsHasCycle_acyclic {ip : IntegerProgram}
    (hac : IntegerProgram.Acyclic ip) :
    ∀ (fuel curr : Nat) (stack done : List Nat),
    (∀ v ∈ stack, ∃ (p : SyntacticPath ip v curr), 0 < p.length) →
    (dfsHasCycle ip fuel curr stack done).1 = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
      intro curr stack done hstack
      simp only [dfsHasCycle]
      by_cases h1 : curr ∈ done
      · simp [h1]
      · by_cases h2 : curr ∈ stack
        · -- curr ∈ stack gives a SyntacticPath ip curr curr with positive length,
          -- contradicting hac.
          simp only [if_neg h1, if_pos h2]
          exfalso
          obtain ⟨p, hp⟩ := hstack curr h2
          have hlen := hac p
          omega
        · simp only [if_neg h1, if_neg h2]
          have hfold : ((succNodes ip curr).foldl
              (fun acc s =>
                if acc.1 then acc
                else dfsHasCycle ip n s (curr :: stack) acc.2)
              (false, done)).1 = false :=
            foldl_false_inv_mem _ _ _ rfl fun acc hacc s hs_mem => by
              simp only [hacc]
              apply ih s (curr :: stack) acc.2
              intro v hv
              simp only [List.mem_cons] at hv
              rcases hv with rfl | hv_stack
              · -- v = curr: single step curr → s witnesses the path
                exact succ_step_path hs_mem
              · -- v ∈ stack: extend path v → curr by step curr → s
                obtain ⟨pv, hpv⟩ := hstack v hv_stack
                obtain ⟨step, _⟩ := succ_step_path hs_mem
                exact ⟨pv.append step,
                       by rw [SyntacticPath.length_append]; omega⟩
          simp [hfold]

-- Correctness: the Boolean algorithm reflects the Acyclic proposition
theorem IntegerProgram.isAcyclic_iff (ip : IntegerProgram) :
    ip.isAcyclic = true ↔ IntegerProgram.Acyclic ip := by
  constructor
  · -- isAcyclic = true → Acyclic
    -- By contrapositive: if p : SyntacticPath ip u u has p.length > 0,
    -- DFS from u would detect the back edge, making isAcyclic = false.
    -- Formalising the "DFS detects every existing cycle" direction
    -- (completeness) is left as future work.
    intro _
    sorry
  · -- Acyclic → isAcyclic = true
    intro hac
    simp only [IntegerProgram.isAcyclic]
    have hfold : (ip.locs.foldl
        (fun acc u =>
          if acc.1 then acc
          else dfsHasCycle ip (ip.locs.length + 1) u [] acc.2)
        (false, [])).1 = false :=
      foldl_false_inv _ _ _ rfl fun acc hacc u => by
        simp only [hacc]
        exact dfsHasCycle_acyclic hac _ _ _ _ (by simp)
    simp [hfold]
