import leantermination.Termination.AcyclicGraph
import leantermination.Datastructures.IntegerProgram


def IntegerProgram.edgePairs (ip : IntegerProgram) : List (Nat × Nat) :=
  ip.edges.map (fun t => (t.src, t.tgt))

def IntegerProgram.toPGraph (ip : IntegerProgram) : PGraph :=
  {
    nodes := ip.locs
    edges := ip.edgePairs
    h_mem := by
      intro e he
      simp only [edgePairs] at he
      simp only [List.mem_map] at he
      rcases he with ⟨t, ht, rfl⟩
      have h := ip.h_edges t ht
      exact h
  }

-- checks if an IntegerProgram is Acyclic
def IntegerProgram.isAcyclic (ip : IntegerProgram) : Bool :=
  PGraph.isAcyclicDFS ip.toPGraph

-- non acyclic-proof function
def IntegerProgram.isAcyclicUpToSelfLoops (ip : IntegerProgram) : Prop :=
  AcyclicUpToSelfLoops ip.toPGraph


-- soundness proofs
theorem acyclic_impl_bounded_IP
  (ip : IntegerProgram)
  (hac : PGraph.Acyclic ip.toPGraph)
  {u v : Nat}
  (p : PPath ip.toPGraph u v) :
  p.length < ip.locs.length :=
by
  exact acyclic_impl_bounded_PPath ip.toPGraph hac p

-- acyclicity soundness
-- right now not complete! @TODO

private theorem transition_in_edgePairs
    {ip : IntegerProgram} {t : Transition} (ht : t ∈ ip.edges) :
    (t.src, t.tgt) ∈ ip.edgePairs := by
  simp only [IntegerProgram.edgePairs, List.mem_map]
  exact ⟨t, ht, rfl⟩

private theorem edgePairs_gives_transition
    {ip : IntegerProgram} {u v : Nat} (h : (u, v) ∈ ip.edgePairs) :
    ∃ t ∈ ip.edges, t.src = u ∧ t.tgt = v := by
  simp only [IntegerProgram.edgePairs, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨t, ht, hsrc, htgt⟩ := h
  exact ⟨t, ht, hsrc, htgt⟩

private def IPPath.toPPath {ip : IntegerProgram} :
    ∀ {u v : Nat}, IPPath ip u v → PPath ip.toPGraph u v
  | _, _, .nil u hu       => PPath.nil u (by
      show u ∈ ip.toPGraph.nodes; exact hu)
  | _, _, .cons t ht p_rest =>
      PPath.cons
        (show (t.src, t.tgt) ∈ ip.toPGraph.edges from transition_in_edgePairs ht)
        p_rest.toPPath


private theorem IPPath.toPPath_length {ip : IntegerProgram} :
    ∀ {u v : Nat} (p : IPPath ip u v), p.toPPath.length = p.length
  | _, _, .nil _ _        => rfl
  | _, _, .cons _ _ p_rest => by
      simp [IPPath.toPPath, IPPath.length, PPath.length, IPPath.toPPath_length p_rest]
