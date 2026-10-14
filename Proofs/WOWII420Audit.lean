/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII420Proof

namespace WOWII420Audit
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ I, G.Adj u v

def leaves (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 1

def minVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ I).card

/-- An incident triangle is uniquely determined by its opposite edge. -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  edgesOn G (G.neighborFinset v)

def minTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, trianglesAt G v ≤ trianglesAt G w

def residual (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ \ neighborhood G (neighborhood G (leaves G))

def closedMinimum (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  minVertices G ∪ neighborhood G (minVertices G)

noncomputable def sourceMinTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, G.numTrianglesAtVertex v ≤ G.numTrianglesAtVertex w

noncomputable def bound420b (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * ((edgesOn G (closedMinimum G) : ℤ) - 1)
noncomputable def bound420c (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * (((sourceMinTriangles G).card : ℤ) - 1)


/-- Equality means the whole universal source target, not just the witness evaluation. -/
theorem exact420b : False ↔ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420b G := by
  exact ⟨False.elim, fun h => WOWII420Proof.conjecture420b h⟩

theorem exact420c : False ↔ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420c G := by
  exact ⟨False.elim, fun h => WOWII420Proof.conjecture420c h⟩

#print axioms TriangleCountProof.triangle_count
#print axioms WOWII420Proof.witness_connected
#print axioms WOWII420Proof.reserve_disjoint
#print axioms WOWII420Proof.independent_dominating_lower
#print axioms WOWII420Proof.independent_domination_eq
#print axioms WOWII420Proof.residual_empty
#print axioms WOWII420Proof.induced_edge_count
#print axioms WOWII420Proof.minimum_triangles
#print axioms WOWII420Proof.sourceMinTriangles_eq
#print axioms WOWII420Proof.bound420b_eq
#print axioms WOWII420Proof.bound420c_eq
#print axioms WOWII420Proof.conjecture420b
#print axioms WOWII420Proof.conjecture420c
#print axioms exact420b
#print axioms exact420c
end WOWII420Audit
