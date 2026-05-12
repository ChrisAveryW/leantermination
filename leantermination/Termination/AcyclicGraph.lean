import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import leantermination.Datastructures.PGraph
import leantermination
import CertifyingDatalog.GraphValidation.Dfs



theorem PPath.visited_length (p : PPath g u v) :
    p.visited.length = p.length + 1 := by
  induction p with
  | nil  _ _    => simp [visited, length]
  | cons _ _ ih => simp [visited, length, ih]; omega

theorem PPath.visited_mem (p : PPath g u v) :
    ∀ x ∈ p.visited, x ∈ g.nodes := by
  induction p with
  | nil  u hu   =>
      intro x hx
      simp [visited] at hx
      subst hx
      exact hu
  | cons he _ ih =>
      intro x hx
      simp only [visited, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (g.h_mem _ he).1
      · exact ih x hx


def PGraph.Reachable (g : PGraph) (u v : Nat) : Prop :=
  Nonempty (PPath g u v)

def PGraph.Acyclic (g : PGraph) : Prop :=
  ∀ {u : Nat} (p : PPath g u u), p.length = 0


theorem PPath.visited_reachable (p : PPath g u v) :
    ∀ x ∈ p.visited, PGraph.Reachable g u x := by
  induction p with
  | nil  u hu   =>
      intro x hx
      simp [visited] at hx
      subst hx
      exact ⟨PPath.nil x hu⟩
  | cons he q ih =>
      intro x hx
      simp only [visited, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨PPath.nil _ (g.h_mem _ he).1⟩
      · obtain ⟨p'⟩ := ih x hx
        exact ⟨PPath.cons he p'⟩


theorem PPath.visited_nodup (hac : PGraph.Acyclic g) (p : PPath g u v) :
    p.visited.Nodup := by
  induction p with
  | nil  _ _      => exact List.nodup_singleton _
  | cons he q ih  =>
      rw [visited, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨p'⟩ := q.visited_reachable _ hmem
      have hclosed : (PPath.cons he p').length = 0 := hac (PPath.cons he p')
      simp [PPath.length] at hclosed

theorem nodup_sublist_length
    {α : Type*}
    {l ref : List α}
    (hnd : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ ref) :
    l.length ≤ ref.length := by
    classical
  have h1 : l.length = l.toFinset.card := by
    exact (List.toFinset_card_of_nodup hnd).symm
  have h2 : l.toFinset ⊆ ref.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [List.mem_toFinset]
    exact hsub x hx
  have h3 : l.toFinset.card ≤ ref.toFinset.card
    := by
    exact Finset.card_le_card h2
  have h4 : ref.toFinset.card ≤ ref.length := by
    exact List.toFinset_card_le ref
  exact calc
    l.length = l.toFinset.card := h1
    _ ≤ ref.toFinset.card := h3
    _ ≤ ref.length := h4


theorem acyclic_impl_bounded_PPath
    (g : PGraph) (hac : PGraph.Acyclic g) {u v : Nat} (p : PPath g u v) :
    p.length < g.nodes.length := by
  have hnd  : p.visited.Nodup :=
    PPath.visited_nodup hac p
  have hmem : ∀ x ∈ p.visited, x ∈ g.nodes :=
    PPath.visited_mem p
  have hle  : p.visited.length ≤ g.nodes.length :=
    nodup_sublist_length hnd hmem
  rw [PPath.visited_length] at hle
  omega


-- non proof functions
-- remove self loops from the graph

def PGraph.withoutSelfLoops (g : PGraph) : PGraph :=
  { nodes := g.nodes
  , edges := g.edges.filter (fun e => e.1 ≠ e.2)
  , h_mem := by
      intro e he
      simp [List.mem_filter] at he
      exact g.h_mem e he.1 }

def AcyclicUpToSelfLoops (g : PGraph) : Prop :=
  PGraph.Acyclic g.withoutSelfLoops

def PGraph.hasPathOfLength (g : PGraph) (u v : Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0     => u == v
  | n + 1 => g.edges.any (fun e =>
      e.1 == u && g.hasPathOfLength e.2 v n)

/-
-- A cycle of positive length at u: path u→u of length 1..n
def PGraph.hasCycleAt (g : PGraph) (u : Nat) : Bool :=
  (List.range g.nodes.length).any (fun k =>
    g.hasPathOfLength u u (k + 1))  -- k+1 so we skip length 0

def PGraph.isAcyclic (g : PGraph) : Bool :=
  !g.nodes.any g.hasCycleAt
-/

--- Create isAcyclic Library with external resource


-- first step of translation PGraph to PreGraph
def PGraph.toPreGraph (pg : PGraph) : PreGraph Nat :=
  pg.edges.foldl
    (fun acc e => acc.add_vertex_with_predecessors e.2 [e.1])
    (PreGraph.from_vertices pg.nodes)


-- prove completenes of foldl method
private theorem foldl_add_predecessors_complete
    (init : PreGraph Nat) (edges : List (Nat × Nat)) (h : init.complete) :
    (edges.foldl
      (fun acc e => acc.add_vertex_with_predecessors e.2 [e.1]) init).complete := by
  induction edges generalizing init with
  | nil        => exact h
  | cons e es ih =>
      simp only [List.foldl_cons]
      exact ih _ (PreGraph.add_vertex_with_predecessors_still_complete init e.2 [e.1] h)

theorem PGraph.toPreGraph_complete (pg : PGraph) : pg.toPreGraph.complete :=
  foldl_add_predecessors_complete _ _
    (PreGraph.from_vertices_is_complete pg.nodes)

-- translate into actual structure, which is needed
def PGraph.toGraph (pg : PGraph) : Graph Nat :=
  ⟨pg.toPreGraph, pg.toPreGraph_complete⟩


-- check for acyclicity with dfs function from resource
def PGraph.isAcyclicDFS (pg : PGraph) : Bool :=
  match pg.toGraph.verify_via_dfs (fun _ => Except.ok ()) with
  | Except.ok _    => true
  | Except.error _ => false

-- correctness of translation and acyclic check
theorem PGraph.isAcyclicDFS_iff (pg : PGraph) :
    pg.isAcyclicDFS = true ↔ pg.toGraph.isAcyclic := by
  unfold PGraph.isAcyclicDFS
  constructor
  · intro h
    split at h
    · -- case ok: use dfs_semantics to extract isAcyclic
      rename_i heq
      exact ((Graph.dfs_semantics _ _).mp heq).1
    · simp at h
  · intro h
    have heq : pg.toGraph.verify_via_dfs (fun _ => Except.ok ()) = Except.ok () := by
      rw [Graph.dfs_semantics]
      exact ⟨h, fun _ _ => rfl⟩
    simp [heq]
