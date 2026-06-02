import leantermination.Termination.Acyclic
import leantermination.Termination.AcyclicUpToLinearLoops


-- same definition like in Acyclic.lean just slightly adapted to allow self loops
def checkAcyclicUpToSelfLoops (ip : IntegerProgram) (comp : Layering) : Bool :=
  ip.edges.all (fun t => (t.src == t.tgt) || decide (comp t.src < comp t.tgt))

-- same lemma only
private lemma mem_withoutSelfLoops_edges
    {ip : IntegerProgram} {t : Transition}
    (ht : t ∈ ip.withoutSelfLoops.edges) : t ∈ ip.edges ∧ t.src ≠ t.tgt := by
  simp only [IntegerProgram.withoutSelfLoops, IntegerProgram.selfLoops,
    decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at ht
  aesop

-- main soundness theorem
theorem checkAcyclicUpToSelfLoops_sound
    {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclicUpToSelfLoops ip comp = true) :
    IntegerProgram.AcyclicUpToSelfLoops ip := by
  -- AcyclicUpToSelfLoops ip  ≡  Acyclic ip.withoutSelfLoops
  unfold IntegerProgram.AcyclicUpToSelfLoops
  apply checkAcyclic_sound (comp := comp)
  -- remaining goal: checkAcyclic ip.withoutSelfLoops comp = true
  unfold checkAcyclic
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨ht_edge, ht_ne⟩ := mem_withoutSelfLoops_edges ht
  -- the per-edge disjunction for this (non-self-loop) edge of ip
  have hdisj := (List.all_eq_true.mp h) t ht_edge
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hdisj
  rcases hdisj with heq | hlt
  · exact absurd heq ht_ne          -- not a self-loop, so this disjunct is impossible
  · simpa using hlt                 -- hence the layer strictly increases

-- decision api, uses acyclic layering function
def IntegerProgram.isAcyclicUpToSelfLoops (ip : IntegerProgram) : Bool :=
  checkAcyclicUpToSelfLoops ip (computeLayering ip)

-- soundness, only one way completeness not given
theorem IntegerProgram.isAcyclicUpToSelfLoops_sound {ip : IntegerProgram}
    (h : ip.isAcyclicUpToSelfLoops = true) :
    IntegerProgram.AcyclicUpToSelfLoops ip :=
  checkAcyclicUpToSelfLoops_sound h
