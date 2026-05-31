import leantermination.Termination.Acyclic
import leantermination.Termination.AcyclicUpToLinearLoops

/-!
# Acyclicity-up-to-self-loops via the same layering certificate

`IntegerProgram.AcyclicUpToSelfLoops ip` is *defined* as
`IntegerProgram.Acyclic ip.withoutSelfLoops`, so the checker is just the acyclic
checker that tolerates self-loop edges: every edge must either be a self-loop
(`src = tgt`) or strictly increase the layer.

This file deliberately imports both `Acyclic` (for `checkAcyclic`,
`checkAcyclic_sound`, `Layering`, `computeLayering`) and `AcyclicUpToLinearLoops`
(for `withoutSelfLoops`, `selfLoops`, `AcyclicUpToSelfLoops`). No import cycle:
`AcyclicUpToLinearLoops` does not import `Acyclic`.
-/

/-- Checker: every edge is a self-loop or strictly increases the layer. -/
def checkAcyclicUpToSelfLoops (ip : IntegerProgram) (comp : Layering) : Bool :=
  ip.edges.all (fun t => (t.src == t.tgt) || decide (comp t.src < comp t.tgt))

/-- Membership in `withoutSelfLoops.edges` means: an edge that is not a self-loop.

NOTE: the `simp only` set below mirrors the one already used and known to work
in `IntegerProgram.withoutSelfLoops.h_edges`. If your Mathlib version reshapes
the goal slightly, this single line is the only place that needs adjusting. -/
private lemma mem_withoutSelfLoops_edges
    {ip : IntegerProgram} {t : Transition}
    (ht : t ∈ ip.withoutSelfLoops.edges) : t ∈ ip.edges ∧ t.src ≠ t.tgt := by
  simp only [IntegerProgram.withoutSelfLoops, IntegerProgram.selfLoops,
    decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at ht
  aesop

/-- **Soundness.** A passing certificate proves acyclicity-up-to-self-loops. -/
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

-- ============================================================
-- Toolchain Boolean API (reuses the single oracle)
-- ============================================================

/-- Boolean decision procedure for the toolchain. One oracle, read a second way. -/
def IntegerProgram.isAcyclicUpToSelfLoops (ip : IntegerProgram) : Bool :=
  checkAcyclicUpToSelfLoops ip (computeLayering ip)

/-- Toolchain soundness. -/
theorem IntegerProgram.isAcyclicUpToSelfLoops_sound {ip : IntegerProgram}
    (h : ip.isAcyclicUpToSelfLoops = true) :
    IntegerProgram.AcyclicUpToSelfLoops ip :=
  checkAcyclicUpToSelfLoops_sound h
