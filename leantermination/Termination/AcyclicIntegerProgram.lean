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

-- conversion proofs
-- semantic and syntactic equivalence
lemma SemanticPath.exists_syntactic {u : Nat} {v : Nat} {env : Env} {ip : IntegerProgram}
  (p : SemanticPath ip env u v) : Nonempty (SyntacticPath ip u v) := by
  exact ⟨p.toSyntactic⟩

lemma SemanticPath.toSyntactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v) : p.toSyntactic.length = p.length := by
  induction p with
  | nil _ _ _           => rfl
  | cons _ _ _ _ _ _ _ ih =>
      simp [SemanticPath.toSyntactic, SyntacticPath.length, SemanticPath.length, ih]

def SyntacticPath.toPPath {ip : IntegerProgram} {u v : Nat} :
    SyntacticPath ip u v → PPath ip.toPGraph u v
  | .nil u hu =>
      PPath.nil u hu  -- ip.toPGraph.nodes = ip.locs, so hu works directly
  | .cons t ht p =>
      PPath.cons
        (show (t.src, t.tgt) ∈ ip.toPGraph.edges from by
          simp only [IntegerProgram.toPGraph, IntegerProgram.edgePairs, List.mem_map]
          exact ⟨t, ht, rfl⟩)
        p.toPPath

lemma SyntacticPath.toPPath_length {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : p.toPPath.length = p.length := by
  induction p with
  | nil _ _ => rfl
  | cons _ _ _ ih =>
      simp [SyntacticPath.toPPath, PPath.length, SyntacticPath.length, ih]

-- soundness proofs
theorem acyclic_impl_bounded_IP
  (ip : IntegerProgram)
  (hac : PGraph.Acyclic ip.toPGraph)
  {u v : Nat}
  (p : PPath ip.toPGraph u v) :
  p.length < ip.locs.length :=
by
  exact acyclic_impl_bounded_PPath ip.toPGraph hac p

def IntegerProgram.Acyclic (ip : IntegerProgram) : Prop :=
  PGraph.Acyclic ip.toPGraph


theorem Acayclic_impl_Termination
  (ip : IntegerProgram) :
    ip.Acyclic → ip.Termination := by
  unfold IntegerProgram.Acyclic IntegerProgram.Termination
  intro h_acyc
  refine ⟨ip.locs.length, ?_⟩
  intro u e v p
  -- semantic → syntactic
  let s := p.toSyntactic
  have h1 : s.length = p.length := SemanticPath.toSyntactic_length p
  -- syntactic → PPath
  let q := s.toPPath
  have h2 : q.length = s.length := SyntacticPath.toPPath_length s
  -- now h_acyc : PGraph.Acyclic ip.toPGraph, which is what the lemma wants
  have hbound : q.length < ip.locs.length :=
    acyclic_impl_bounded_IP ip h_acyc q
  omega




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
