import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic

/-!
# Correctness of the `IsAcyclic` decision procedure

This file proves `IntegerProgram.isAcyclic_iff`:

    ip.IsAcyclic = true  ↔  ip.Acyclic

The decision procedure is a fuel-bounded reachability computation (`reaches`),
lifted to a per-edge cycle test (`hasCycle`), and negated (`IsAcyclic`).

## Dependency structure

    reaches_iff : reaches u v = true ↔ Nonempty (SyntacticPath ip u v)   (u ∈ locs)
     ├─ soundness  (→) : closure_reachable    (snoc + mem_expand)
     └─ completeness (←): closed_path + closure_closed   ← the crux

    hasCycle_iff  : hasCycle = true ↔ ∃ u, ∃ p : SyntacticPath ip u u, 0 < p.length
    isAcyclic_iff : IsAcyclic = true ↔ Acyclic                          ← Bool glue

Only `closure_closed` is hard; it shows the worklist saturates within
`locs.length` rounds, by the same Nodup/cardinality argument used elsewhere
in this development.

## Notes on version drift
A few spots are sensitive to the exact Mathlib version:
  * `mem_expand`     — depends on how `(· ∉ acc)` elaborates inside `List.filter`.
                       If `expand` does not compile with `.filter (· ∉ acc)`,
                       switch it to `.filter (fun z => !(acc.contains z))` and
                       adjust the `mem_filter` rewrite accordingly.
  * `hasCycle_iff`   — uses dependent `cases` on a `u u`-indexed path.
  * lemma names      — `List.mem_flatMap`/`List.mem_bind`, `decide_eq_true_iff`
                       sometimes drift between releases.
-/


def SyntacticPath.snoc {ip : IntegerProgram} :
    {u x : Nat} → SyntacticPath ip u x → (t : Transition) → t ∈ ip.edges → t.src = x →
    SyntacticPath ip u t.tgt
  | _, _, .nil _ _,       t, h, hx => hx ▸ .cons t h (.nil t.tgt (ip.h_edges t h).2)
  | _, _, .cons t' h' q,  t, h, hx => .cons t' h' (q.snoc t h hx)


-- ===========================================================================
-- Algorithm  (assumed already defined in your file; reproduced here so this
-- file is self-contained. Delete this block if it is defined upstream.)
-- ===========================================================================

namespace IntegerProgram

def succs (ip : IntegerProgram) (u : Nat) : List Nat :=
  (ip.edges.filter (fun t => t.src == u)).map (·.tgt)

/-- one BFS layer -/
def expand (ip : IntegerProgram) (acc : List Nat) : List Nat :=
  (acc ++ (acc.flatMap ip.succs).filter (· ∉ acc)).dedup

/-- saturate, ≤ `fuel` rounds, with early stop at a fixpoint -/
def closure (ip : IntegerProgram) : Nat → List Nat → List Nat
  | 0,      acc => acc
  | fuel+1, acc =>
      let acc' := expand ip acc
      if acc'.length ≤ acc.length then acc else closure ip fuel acc'

def reaches (ip : IntegerProgram) (u v : Nat) : Bool :=
  v ∈ ip.closure ip.locs.length [u]

def hasCycle (ip : IntegerProgram) : Bool :=
  ip.edges.any (fun t => ip.reaches t.tgt t.src)

def IsAcyclic (ip : IntegerProgram) : Bool := !ip.hasCycle

-- ===========================================================================
-- Path surgery: append one edge at the END of a path.
-- (`SyntacticPath.cons` only prepends; soundness extends at the far end.)
-- ===========================================================================


-- ===========================================================================
-- Membership characterizations for `succs` and `expand`.
-- ===========================================================================

lemma mem_succs (ip : IntegerProgram) (u v : Nat) :
    v ∈ ip.succs u ↔ ∃ t ∈ ip.edges, t.src = u ∧ t.tgt = v := by
  simp only [succs, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨t, ⟨ht, hsrc⟩, htgt⟩; exact ⟨t, ht, hsrc, htgt⟩
  · rintro ⟨t, ht, hsrc, htgt⟩; exact ⟨t, ⟨ht, hsrc⟩, htgt⟩

lemma succs_subset_locs (ip : IntegerProgram) {u v : Nat} (h : v ∈ ip.succs u) :
    v ∈ ip.locs := by
  obtain ⟨t, ht, _, htv⟩ := (mem_succs ip u v).mp h
  exact htv ▸ (ip.h_edges t ht).2

-- ⚠ The filter-predicate shape on the RHS may differ; if so, fix the
--   `mem_filter` rewrite (or the `expand` definition itself).
lemma mem_expand (ip : IntegerProgram) (acc : List Nat) (x : Nat) :
    x ∈ ip.expand acc ↔ x ∈ acc ∨ ∃ y ∈ acc, x ∈ ip.succs y := by
  unfold expand
  rw [List.mem_dedup, List.mem_append, List.mem_filter, List.mem_flatMap]
  constructor
  · rintro (hx | ⟨⟨y, hy, hyx⟩, _⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨y, hy, hyx⟩
  · rintro (hx | ⟨y, hy, hyx⟩)
    · exact Or.inl hx
    · by_cases hxa : x ∈ acc
      · exact Or.inl hxa
      · exact Or.inr ⟨⟨y, hy, hyx⟩, by simpa using hxa⟩

lemma subset_expand (ip : IntegerProgram) (acc : List Nat) :
    ∀ x ∈ acc, x ∈ ip.expand acc := fun x hx => (mem_expand ip acc x).mpr (Or.inl hx)

lemma expand_nodup (ip : IntegerProgram) (acc : List Nat) : (ip.expand acc).Nodup :=
  List.nodup_dedup _

lemma expand_subset_locs (ip : IntegerProgram) (acc : List Nat)
    (h : ∀ x ∈ acc, x ∈ ip.locs) : ∀ x ∈ ip.expand acc, x ∈ ip.locs := by
  intro x hx
  rcases (mem_expand ip acc x).mp hx with hxa | ⟨y, _, hyx⟩
  · exact h x hxa
  · exact succs_subset_locs ip hyx

-- ===========================================================================
-- `closure` only grows its accumulator.
-- ===========================================================================

lemma subset_closure (ip : IntegerProgram) :
    ∀ (fuel : Nat) (acc : List Nat), ∀ x ∈ acc, x ∈ ip.closure fuel acc := by
  intro fuel
  induction fuel with
  | zero => intro acc x hx; simpa only [closure] using hx
  | succ fuel ih =>
      intro acc x hx
      simp only [closure]
      split
      · exact hx
      · exact ih _ x (subset_expand ip acc x hx)

-- ===========================================================================
-- Finite-set helpers (same flavour as `nodup_sublist_length`).
-- ===========================================================================

lemma nodup_len_le {l ref : List Nat} (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ ref) :
    l.length ≤ ref.length := by
  classical
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ ref.toFinset.card :=
        Finset.card_le_card (by intro x hx; rw [List.mem_toFinset] at *; exact hsub x hx)
    _ ≤ ref.length := List.toFinset_card_le ref

/-- If `a ⊆ b`, both nodup, and `|b| ≤ |a|`, then `b ⊆ a` (same elements). -/
lemma sub_of_nodup_len {a b : List Nat} (ha : a.Nodup) (hb : b.Nodup)
    (hsub : ∀ x ∈ a, x ∈ b) (hlen : b.length ≤ a.length) : ∀ x ∈ b, x ∈ a := by
  classical
  have hsubF : a.toFinset ⊆ b.toFinset := by
    intro x hx; rw [List.mem_toFinset] at *; exact hsub x hx
  have hcard : b.toFinset.card ≤ a.toFinset.card := by
    rw [List.toFinset_card_of_nodup ha, List.toFinset_card_of_nodup hb]; exact hlen
  have heq : a.toFinset = b.toFinset := Finset.eq_of_subset_of_card_le hsubF hcard
  intro x hx
  have hxF : x ∈ b.toFinset := List.mem_toFinset.mpr hx
  rw [← heq, List.mem_toFinset] at hxF; exact hxF

/-- A nodup `acc ⊆ locs` with `|acc| ≥ |locs|` already contains all of `locs`. -/
lemma acc_covers_locs (ip : IntegerProgram) {acc : List Nat}
    (hnd : acc.Nodup) (hsub : ∀ x ∈ acc, x ∈ ip.locs)
    (hlen : ip.locs.length ≤ acc.length) : ∀ z ∈ ip.locs, z ∈ acc := by
  classical
  have hsubF : acc.toFinset ⊆ ip.locs.toFinset := by
    intro x hx; rw [List.mem_toFinset] at *; exact hsub x hx
  have hge : ip.locs.toFinset.card ≤ acc.toFinset.card := by
    have h1 := List.toFinset_card_of_nodup hnd
    have h2 := List.toFinset_card_le ip.locs
    omega
  have heq : acc.toFinset = ip.locs.toFinset := Finset.eq_of_subset_of_card_le hsubF hge
  intro z hz
  have hzF : z ∈ ip.locs.toFinset := List.mem_toFinset.mpr hz
  rw [← heq, List.mem_toFinset] at hzF; exact hzF

-- ===========================================================================
-- Soundness: everything in `closure` is genuinely reachable.
-- ===========================================================================

lemma closure_reachable (ip : IntegerProgram) (u : Nat) :
    ∀ (fuel : Nat) (acc : List Nat),
      (∀ x ∈ acc, Nonempty (SyntacticPath ip u x)) →
      ∀ x ∈ ip.closure fuel acc, Nonempty (SyntacticPath ip u x) := by
  intro fuel
  induction fuel with
  | zero => intro acc hr x hx; simp only [closure] at hx; exact hr x hx
  | succ fuel ih =>
      intro acc hr x hx
      simp only [closure] at hx
      split at hx
      · exact hr x hx
      · refine ih (ip.expand acc) ?_ x hx
        intro z hz
        rcases (mem_expand ip acc z).mp hz with hza | ⟨y, hy, hyz⟩
        · exact hr z hza
        · obtain ⟨py⟩ := hr y hy
          obtain ⟨t, ht, hts, htz⟩ := (mem_succs ip y z).mp hyz
          exact ⟨htz ▸ py.snoc t ht hts⟩

-- ===========================================================================
-- Completeness core: a path cannot leave a succ-closed set.
-- ===========================================================================

lemma closed_path (ip : IntegerProgram) (S : List Nat)
    (hcl : ∀ x ∈ S, ∀ y ∈ ip.succs x, y ∈ S) :
    ∀ {u v : Nat}, SyntacticPath ip u v → u ∈ S → v ∈ S := by
  intro u v p
  induction p with
  | nil _ _ => intro h; exact h
  | cons t ht q ih =>
      intro hu
      exact ih (hcl t.src hu t.tgt ((mem_succs ip t.src t.tgt).mpr ⟨t, ht, rfl, rfl⟩))

-- ===========================================================================
-- THE CRUX: `closure` is closed under `succs`.
--
-- Invariant carried through the fuel induction:
--     locs.length ≤ fuel + acc.length
-- Each non-early-stop round grows `acc` by ≥ 1, so within `locs.length`
-- rounds the worklist saturates and becomes closed under `succs`.
-- ===========================================================================

lemma closure_closed (ip : IntegerProgram) :
    ∀ (fuel : Nat) (acc : List Nat),
      acc.Nodup → (∀ x ∈ acc, x ∈ ip.locs) → ip.locs.length ≤ fuel + acc.length →
      ∀ x ∈ ip.closure fuel acc, ∀ y ∈ ip.succs x, y ∈ ip.closure fuel acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro acc hnd hsub hfuel
      simp only [closure]
      intro x _ y hy
      -- fuel = 0 forces locs.length ≤ acc.length, so acc already covers locs
      have hcov := acc_covers_locs ip hnd hsub (by simpa using hfuel)
      exact hcov y (succs_subset_locs ip hy)
  | succ fuel ih =>
      intro acc hnd hsub hfuel
      simp only [closure]
      split
      case isTrue h =>
        -- early stop: expand acc has the same elements as acc ⟹ acc is closed
        intro x hx y hy
        have hyexp : y ∈ ip.expand acc := (mem_expand ip acc y).mpr (Or.inr ⟨x, hx, hy⟩)
        exact sub_of_nodup_len hnd (expand_nodup ip acc) (subset_expand ip acc) h y hyexp
      case isFalse h =>
        -- progress: |expand acc| > |acc|, so the fuel invariant survives
        exact ih (ip.expand acc) (expand_nodup ip acc)
          (expand_subset_locs ip acc hsub) (by omega)

-- ===========================================================================
-- The spec lemma: `reaches` exactly captures path-existence.
-- ===========================================================================

lemma reaches_iff (ip : IntegerProgram) {u v : Nat} (hu : u ∈ ip.locs) :
    ip.reaches u v = true ↔ Nonempty (SyntacticPath ip u v) := by
  unfold reaches
  rw [decide_eq_true_iff]
  constructor
  · -- soundness
    intro h
    refine closure_reachable ip u ip.locs.length [u] ?_ v h
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨.nil u hu⟩
  · -- completeness
    rintro ⟨p⟩
    have hclosed := closure_closed ip ip.locs.length [u]
      (List.nodup_singleton u)
      (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hu)
      (by simp only [List.length_singleton]; omega)
    have huin : u ∈ ip.closure ip.locs.length [u] :=
      subset_closure ip ip.locs.length [u] u (List.mem_singleton_self u)
    exact closed_path ip _ hclosed p huin

-- ===========================================================================
-- Glue: `hasCycle` ↔ a nontrivial closed path exists.
-- ===========================================================================

lemma hasCycle_iff (ip : IntegerProgram) :
    ip.hasCycle = true ↔ ∃ (u : Nat) (p : SyntacticPath ip u u), 0 < p.length := by
  unfold hasCycle
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hr⟩
    have htgt : t.tgt ∈ ip.locs := (ip.h_edges t ht).2
    obtain ⟨q⟩ := (reaches_iff ip htgt).mp hr        -- q : SyntacticPath ip t.tgt t.src
    exact ⟨t.src, .cons t ht q, by simp [SyntacticPath.length]⟩
  · rintro ⟨u, p, hpos⟩
    cases p with                                      -- dependent cases on a `u u` path
    | nil _ _ => simp [SyntacticPath.length] at hpos
    | cons t ht q =>                                  -- u ≡ t.src, q : t.tgt → t.src
        exact ⟨t, ht, (reaches_iff ip (ip.h_edges t ht).2).mpr ⟨q⟩⟩

-- ===========================================================================
-- Main theorem.
-- ===========================================================================

theorem isAcyclic_iff (ip : IntegerProgram) : ip.IsAcyclic = true ↔ ip.Acyclic := by
  constructor
  · -- IsAcyclic ⟹ Acyclic
    intro h u p
    by_contra hne
    have hcy := (hasCycle_iff ip).mpr ⟨u, p, Nat.pos_of_ne_zero hne⟩
    unfold IsAcyclic at h
    rw [hcy] at h
    simp at h
  · -- Acyclic ⟹ IsAcyclic
    intro hac
    unfold IsAcyclic
    cases hcy : ip.hasCycle with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨u, p, hpos⟩ := (hasCycle_iff ip).mp hcy
        have := hac p
        omega

end IntegerProgram
