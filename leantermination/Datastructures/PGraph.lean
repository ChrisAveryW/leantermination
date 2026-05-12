
structure PGraph where
  nodes : List Nat
  edges : List (Nat × Nat)
  h_mem : ∀ e ∈ edges, e.1 ∈ nodes ∧ e.2 ∈ nodes

-- Example 1:
def _PGraph : PGraph := {nodes := [1,2,3], edges := [(1,3), (2,1)], h_mem := by decide}
#eval _PGraph


inductive PPath (g : PGraph) : Nat → Nat → Type where
  | nil  : (u : Nat) → u ∈ g.nodes → PPath g u u
  | cons : {u w v : Nat} → (u, w) ∈ g.edges → PPath g w v → PPath g u v

-- Example 2:
def _PPath13 : PPath _PGraph 1 3 :=
  PPath.cons (by decide) (PPath.nil 3 (by decide))

def _PPath23 : PPath _PGraph 2 3 :=
  PPath.cons (by decide) _PPath13

def PPath.length : PPath g u v → Nat
  | .nil  _ _   => 0
  | .cons _ p   => 1 + p.length

-- Example 3:
#eval _PPath23.length


def PPath.visited : PPath g u v → List Nat
  | .nil  u _   => [u]
  | .cons _ p   => u :: p.visited

-- Example 4:
#eval _PPath23.visited
