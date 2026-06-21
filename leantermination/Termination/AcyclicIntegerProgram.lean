import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic

/-
Some helper lemmas about Paths.
-/


/--
This lemma shows that the function `SemanticPath.toSyntactic` preserves length.
It works by induction over the two cases of a SemanticPath.
-/
private lemma SemanticPath.toSyntactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v) : p.toSyntactic.length = p.length := by
  induction p with
  | nil _ _ _           => rfl
  | cons _ _ _ _ _ _ _ ih =>
      simp only [SemanticPath.toSyntactic, SyntacticPath.length, SemanticPath.length, ih]

/--
This lemma just changes the interaction of the `SemanticPath.toSyntatctic_length` lemma.
It doesn't introduce any new knowledge.
-/
private lemma SemanticPath.synatactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v)
    (p' : SyntacticPath ip u v)
    (h_eq : p.toSyntactic = p') :
    p'.length = p.length := by
  rw [← h_eq]
  rw [SemanticPath.toSyntactic_length]

/--
This lemma proves that the length of `SyntacticPath` stands in a specific relation to the length
of visited locations. The number of visited locations is always one more than the path length.
This is because the path length is defined on the number of transitions.
-/
private lemma SyntacticPath.visited_length {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : p.visited.length = p.length + 1 := by
  induction p with
  | nil _ _       => simp only [visited, List.length_cons, List.length_nil, zero_add, length]
  | cons _ _ _ ih =>
    simp only [visited, List.length_cons, ih, length, Nat.add_right_cancel_iff]
    omega

private lemma SyntacticPath.visited_mem {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : ∀ x ∈ p.visited, x ∈ ip.locs := by
  induction p with
  | nil u hu =>
      intro x hx
      simp only [visited, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact hu
  | cons t ht _ ih =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (ip.h_edges t ht).1
      · exact ih x hx

private lemma SyntacticPath.visited_reachable {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : ∀ x ∈ p.visited, Nonempty (SyntacticPath ip u x) := by
  induction p with
  | nil u hu =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_singleton] at hx
      rw [hx]
      exact ⟨.nil u hu⟩
  | cons t ht q ih =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.nil t.src (ip.h_edges t ht).1⟩
      · obtain ⟨p'⟩ := ih x hx
        exact ⟨.cons t ht p'⟩

private lemma SyntacticPath.visited_nodup {ip : IntegerProgram}
    (hac : IntegerProgram.Acyclic ip) {u v : Nat}
    (p : SyntacticPath ip u v) : p.visited.Nodup := by
  induction p with
  | nil u' _ => exact List.nodup_singleton u'
  | cons t ht q ih =>
      rw [SyntacticPath.visited, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨p'⟩ := q.visited_reachable _ hmem
      have hcycle : (.cons t ht p' : SyntacticPath ip t.src t.src).length = 0 := hac _
      simp only [SyntacticPath.length] at hcycle
      omega

private lemma nodup_sublist_length {α : Type*} {l ref : List α}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ ref) : l.length ≤ ref.length := by
  classical
  have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have h2 : l.toFinset ⊆ ref.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at *
    exact hsub x hx
  exact calc l.length = l.toFinset.card   := h1
    _                 ≤ ref.toFinset.card := Finset.card_le_card h2
    _                 ≤ ref.length        := List.toFinset_card_le ref

theorem acyclic_impl_bounded_SyntacticPath
    {ip : IntegerProgram} {u v : Nat}
    (h_acyc : IntegerProgram.Acyclic ip)
    (p : SyntacticPath ip u v) :
    p.length < ip.locs.length := by
  have h_nodup  := SyntacticPath.visited_nodup h_acyc p
  have h_mem := SyntacticPath.visited_mem p
  have h_le  := nodup_sublist_length h_nodup h_mem
  rw [SyntacticPath.visited_length] at h_le
  omega


-- Main Acyclic theorem
theorem Acayclic_impl_Termination (ip : IntegerProgram) :
    IntegerProgram.Acyclic ip → IntegerProgram.Termination ip := by
  intro h_acyc
  unfold IntegerProgram.Termination
  intro e
  refine ⟨ip.locs.length, ?_⟩
  intro u v p
  let syntactic_path := p.toSyntactic
  have h_eq : p.toSyntactic = syntactic_path := rfl
  have h1 := acyclic_impl_bounded_SyntacticPath h_acyc syntactic_path
  rw [SemanticPath.synatactic_length p syntactic_path h_eq] at h1
  omega
