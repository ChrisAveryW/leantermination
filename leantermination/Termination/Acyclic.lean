import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate

open Function

/-!
# Acyclicity via a layering certificate

This replaces the previous DFS-based `isAcyclic` with the *certifying checker*
pattern:

  * an (untrusted) oracle produces a layering `comp : Nat → Nat`;
  * a small verified checker validates that `comp` strictly increases along
    every edge;
  * soundness (`checkAcyclic_sound`) proves that a passing certificate implies
    `IntegerProgram.Acyclic`.

Only **soundness** (`checker = true → Acyclic`) is needed for the toolchain to
be correct: a `true` result is trustworthy; a `false` result merely means
"could not certify". We therefore do **not** prove completeness — which removes
the previous `sorry` in `isAcyclic_iff` and lets us delete the entire DFS.

The oracle `computeLayering` is deliberately untrusted: a wrong `comp` can only
ever make the checker *reject* (a completeness gap), never make it accept a
cyclic program (a strictly-increasing layering cannot exist around a cycle).
-/

/-- A layering certificate: a numbering of locations. Untrusted data. -/
abbrev Layering := Nat → Nat

-- ============================================================
-- Verified checker + soundness  (the part that matters)
-- ============================================================

/-- Checker for plain acyclicity: every edge strictly increases the layer. -/
def checkAcyclic (ip : IntegerProgram) (comp : Layering) : Bool :=
  ip.edges.all (fun t => decide (comp t.src < comp t.tgt))

/-- Extract the per-edge fact from a passing certificate. -/
lemma checkAcyclic_edge {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclic ip comp = true) :
    ∀ t ∈ ip.edges, comp t.src < comp t.tgt := by
  intro t ht
  have hb := (List.all_eq_true.mp h) t ht
  simpa using hb

/-- Core invariant: along any syntactic path the layer grows by at least the
length of the path. -/
lemma checkAcyclic_layer_mono {ip : IntegerProgram} {comp : Layering}
    (hedge : ∀ t ∈ ip.edges, comp t.src < comp t.tgt)
    {u v : Nat} (p : SyntacticPath ip u v) :
    comp u + p.length ≤ comp v := by
  induction p with
  | nil u h => simp [SyntacticPath.length]
  | cons t h p' ih =>
      -- u = t.src ; p' : SyntacticPath ip t.tgt v ; length = 1 + p'.length
      have hlt := hedge t h            -- comp t.src < comp t.tgt
      simp only [SyntacticPath.length]
      -- goal: comp t.src + (1 + p'.length) ≤ comp v ;  ih: comp t.tgt + p'.length ≤ comp v
      omega

/-- **Soundness.** A passing layering certificate proves acyclicity. -/
theorem checkAcyclic_sound {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclic ip comp = true) : IntegerProgram.Acyclic ip := by
  unfold IntegerProgram.Acyclic
  intro u p
  have hmono := checkAcyclic_layer_mono (checkAcyclic_edge h) p  -- comp u + p.length ≤ comp u
  omega

-- ============================================================
-- Untrusted oracle (swappable; correctness NOT relied upon)
-- ============================================================

/-!
`computeLayering` is **not** verified. A longest-path relaxation: iterate
`comp t.tgt := max (comp t.tgt) (comp t.src + 1)` over all edges `locs.length+1`
times. For an acyclic program this converges to a strict layering; for a cyclic
program some back-edge necessarily fails the checker.

Swap this for Mathlib's `Mathlib.Tactic.Order.Graph.findSCCs` + a topological
numbering, or any heuristic — soundness is unaffected. If it ever fails to
compile in your toolchain, temporarily use `fun _ => 0` (which makes every check
fail *safely*) until the real oracle is wired in.
-/
private def relaxOnce (edges : List Transition) (comp : Nat → Nat) : Nat → Nat :=
  edges.foldl
    (fun c t => Function.update c t.tgt (max (c t.tgt) (c t.src + 1)))
    comp

def computeLayering (ip : IntegerProgram) : Layering :=
  (relaxOnce ip.edges)^[ip.locs.length + 1] (fun _ => 0)

-- ============================================================
-- Toolchain Boolean API (names kept stable for CheckAcyclic.lean)
-- ============================================================

/-- Boolean decision procedure used by the toolchain. -/
def IntegerProgram.isAcyclic (ip : IntegerProgram) : Bool :=
  checkAcyclic ip (computeLayering ip)

/-- Toolchain soundness: a `true` answer proves acyclicity. -/
theorem IntegerProgram.isAcyclic_sound {ip : IntegerProgram}
    (h : ip.isAcyclic = true) : IntegerProgram.Acyclic ip :=
  checkAcyclic_sound h
