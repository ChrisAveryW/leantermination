# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
# Build everything
lake build

# Build and run the main executable (SMT/Z3 termination check)
lake exe main

# Build and run the acyclicity checker on a .ari file
lake exe check

# Check if a specific file compiles
lake build leantermination.Termination.AcyclicIntegerProgram
```

Lean 4 version is pinned to `leanprover/lean4:v4.29.0`. Dependencies are Mathlib (v4.29.0) and CertifyingDatalog.

## Architecture

This is a Bachelor's thesis formalizing **termination checking of Integer Programs** in Lean 4.

### Core data structure (`Datastructures/IntegerProgram.lean`)

- `IntegerProgram` holds `locs : List Nat`, `l₀ : Nat` (start location), `edges : List Transition`, and `h_edges` (proof that all transition src/tgt are in `locs`).
- `Transition` = `{src, tgt : Nat, guard : Constraint, update : List Update}`.
- `SyntacticPath ip u v` — an inductive path type through the *graph* (ignoring guards/state). Used for acyclicity arguments.
- `SemanticPath ip env u v` — a path that also carries a concrete `Env` and requires guards to hold. Used for termination bounds.
- `IntegerProgram.Acyclic ip` is the *propositional* notion: `∀ {u} (p : SyntacticPath ip u u), p.length = 0`.
- `IntegerProgram.Termination ip` says execution lengths are uniformly bounded for any start state.

### Termination proofs (`Termination/`)

- **`AcyclicIntegerProgram.lean`** — proves `Acyclic → Termination`. Key chain: `SyntacticPath.visited_nodup` (acyclicity ⟹ no repeated nodes in visited list) + `nodup_sublist_length` ⟹ `path.length < locs.length`.
- **`LASWTermination.lean`** — proves termination via a linear ranking function. Uses a `FarkasWitness` (λ₁, λ₂, A, A', b) satisfying four Farkas conditions. Constructs ranking function `ρ = λ₂·A'·env` and proves it strictly decreases by `δ > 0` on every step, giving a finite path-length bound.
- **`AcyclicUpToLinearLoops.lean`** — handles programs with self-loops separately: decomposes path length into skeleton steps (acyclic subgraph, bounded by `locs.length`) + self-loop steps (bounded via per-self-loop Farkas witnesses). `total_selfloop_steps_bounded` is currently `sorry`.
- **`Acyclic.lean`** — currently empty; the target for `IntegerProgram.isAcyclic` (decidable algorithm) + its correctness proof.

### Toolchain (`Toolchain/CheckAcyclic.lean`)

Executable (`lake exe check`) that parses a `.ari` file and calls `IntegerProgram.IsAcyclic`. Currently references `isAcyclic`/`IsAcyclic` which must be implemented in `Termination/Acyclic.lean`.

### Parsing (`Parsing/`)

- `Preparse.lean` — s-expression tokenizer/parser for the `.ari` ITS format.
- `ITSParse.lean` — translates `ParsedITS` → `IntegerProgram`, building location and variable index maps.

Test `.ari` files live in `leantermination/Data/IntegerPrograms/{Well-Formed,Badly-Formed,Acyclic}/`.

### Learning/ directory

Exploratory/scratch files from earlier development. `AcyclicFinite_clean.lean` contains an older attempt at a `rank`-based acyclicity proof (with `sorry`s). These are not imported by the main build.

## Key design choices

- **Acyclicity is syntactic**: `IntegerProgram.Acyclic` quantifies over `SyntacticPath` (no guards), making it decidable in principle purely from the graph structure.
- **`isAcyclic` should target `IntegerProgram.Acyclic`**: The intended correctness statement is `isAcyclic ip = true ↔ IntegerProgram.Acyclic ip`. A DFS/topological-sort-based Boolean function on `ip.locs` and `ip.edges` is the natural approach, since `Acyclic` is about the pure directed graph.
- **`relaxedAutoImplicit = false`** is set globally — all variables must be explicitly introduced.
