import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import leantermination.Datastructures.IntegerProgram
import leantermination


-- Semantic Path to Syntactic Paths

private lemma SemanticPath.exists_syntactic {u v : Nat} {env : Env} {ip : IntegerProgram}
    (p : SemanticPath ip env u v) : Nonempty (SyntacticPath ip u v) :=
  ⟨p.toSyntactic⟩

private lemma SemanticPath.toSyntactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v) : p.toSyntactic.length = p.length := by
  induction p with
  | nil _ _ _           => rfl
  | cons _ _ _ _ _ _ _ ih =>
      simp [SemanticPath.toSyntactic, SyntacticPath.length, SemanticPath.length, ih]


-- Helper functions and Lemma for

def SyntacticPath.visited {ip : IntegerProgram} {u v : Nat} :
    SyntacticPath ip u v → List Nat
  | .nil u _    => [u]
  | .cons t _ p => t.src :: p.visited

private lemma SyntacticPath.visited_length {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : p.visited.length = p.length + 1 := by
  induction p with
  | nil _ _       => simp [SyntacticPath.visited, SyntacticPath.length]
  | cons _ _ _ ih => simp [SyntacticPath.visited, SyntacticPath.length, ih]; omega

private lemma SyntacticPath.visited_mem {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : ∀ x ∈ p.visited, x ∈ ip.locs := by
  induction p with
  | nil u hu =>
      intro x hx
      simp only [visited, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; exact hu
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
  | nil _ _ => exact List.nodup_singleton _
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

theorem acyclic_impl_bounded_SyntacticPath {ip : IntegerProgram}
    (hac : IntegerProgram.Acyclic ip) {u v : Nat} (p : SyntacticPath ip u v) :
    p.length < ip.locs.length := by
  have hnd  := SyntacticPath.visited_nodup hac p
  have hmem := SyntacticPath.visited_mem p
  have hle  := nodup_sublist_length hnd hmem
  rw [SyntacticPath.visited_length] at hle
  omega


-- Main Acyclic theorem
theorem Acayclic_impl_Termination (ip : IntegerProgram) :
    IntegerProgram.Acyclic ip → IntegerProgram.Termination ip := by
  intro h_acyc
  unfold IntegerProgram.Termination
  intro e
  refine ⟨ip.locs.length, ?_⟩
  intro u v p
  have h1 := SemanticPath.toSyntactic_length p
  have h2 := acyclic_impl_bounded_SyntacticPath h_acyc p.toSyntactic
  rw [SemanticPath.toSyntactic_length] at h2
  omega
