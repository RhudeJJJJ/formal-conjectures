/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Actual graph Laplacian identities for the pendant-path fusion formalization.
These lemmas do not assume or assert the strict fusion inequality.
-/
import Proofs.RadenkovicGutmanSpectral
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Gebendorfer.RadenkovicGutman

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Graph union gives Laplacian addition when the edge sets are disjoint. -/
theorem lapMatrix_sup_of_disjoint (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : Disjoint G H) :
    (G ⊔ H).lapMatrix ℝ = G.lapMatrix ℝ + H.lapMatrix ℝ := by
  have hd (v : V) : (G ⊔ H).degree v = G.degree v + H.degree v := by
    unfold SimpleGraph.degree
    rw [SimpleGraph.neighborFinset_sup_of_disjoint v h, Finset.card_disjUnion]
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply]
  by_cases hij : i = j
  · subst j
    simp [hd]
  · have hnot : ¬(G.Adj i j ∧ H.Adj i j) := by
      intro hx
      exact SimpleGraph.disjoint_left.mp h i j hx.1 hx.2
    simp only [hij, if_false, zero_sub, SimpleGraph.sup_adj]
    by_cases hg : G.Adj i j <;> by_cases hh : H.Adj i j <;> simp_all

/-- The incidence vector of an oriented edge; the outer product is orientation-free. -/
def edgeVector (u w : V) : V → ℝ :=
  fun x => (if x = u then 1 else 0) - (if x = w then 1 else 0)

/-- A single edge contributes exactly its incidence-vector outer product. -/
theorem lapMatrix_edge (u w : V) (huw : u ≠ w) :
    (SimpleGraph.edge u w).lapMatrix ℝ =
      Matrix.vecMulVec (edgeVector u w) (edgeVector u w) := by
  have hnu : (SimpleGraph.edge u w).neighborFinset u = {w} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj,
      Finset.mem_singleton]
    aesop
  have hnw : (SimpleGraph.edge u w).neighborFinset w = {u} := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj,
      Finset.mem_singleton]
    aesop
  have hno (x : V) (hxu : x ≠ u) (hxw : x ≠ w) :
      (SimpleGraph.edge u w).neighborFinset x = ∅ := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj, hxu, hxw]
  have hd (x : V) : (SimpleGraph.edge u w).degree x =
      if x = u ∨ x = w then 1 else 0 := by
    by_cases hxu : x = u
    · subst x
      simp only [SimpleGraph.degree, hnu, Finset.card_singleton, true_or, ite_true]
    · by_cases hxw : x = w
      · subst x
        simp only [SimpleGraph.degree, hnw, Finset.card_singleton, or_true, ite_true]
      · simp only [SimpleGraph.degree, hno x hxu hxw, Finset.card_empty,
          hxu, hxw, or_self, ite_false]
  ext i j
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Matrix.vecMulVec_apply,
    edgeVector]
  rw [hd i]
  clear hd hnu hnw hno
  by_cases hiu : i = u <;> by_cases hiw : i = w <;>
    by_cases hju : j = u <;> by_cases hjw : j = w <;>
      simp_all [SimpleGraph.edge_adj] <;> aesop

/-- Replacing one edge has the exact difference of two rank-one matrices. -/
theorem rewire_laplacian_difference (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v w : V) (huw : u ≠ w) (hvw : v ≠ w)
    (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w) :
    (G ⊔ SimpleGraph.edge u w).lapMatrix ℝ -
        (G ⊔ SimpleGraph.edge v w).lapMatrix ℝ =
      Matrix.vecMulVec (edgeVector u w) (edgeVector u w) -
        Matrix.vecMulVec (edgeVector v w) (edgeVector v w) := by
  rw [lapMatrix_sup_of_disjoint G _ ((SimpleGraph.disjoint_edge G).mpr hguw),
    lapMatrix_sup_of_disjoint G _ ((SimpleGraph.disjoint_edge G).mpr hgvw),
    lapMatrix_edge u w huw, lapMatrix_edge v w hvw]
  abel

/-- Evaluation of an incidence-vector dot product, independent of the graph. -/
theorem edgeVector_dot (u w : V) (x : V → ℝ) :
    edgeVector u w ⬝ᵥ x = x u - x w := by
  unfold edgeVector dotProduct
  simp_rw [sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- The two vectors in a three-distinct-vertex rewiring have norms squared two
and inner product one. These are exact equalities over the real numbers. -/
theorem rewire_gram (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    edgeVector u w ⬝ᵥ edgeVector u w = 2 ∧
    edgeVector v w ⬝ᵥ edgeVector v w = 2 ∧
    edgeVector u w ⬝ᵥ edgeVector v w = 1 := by
  norm_num [edgeVector_dot, edgeVector, huw, hvw, huv, Ne.symm huw, Ne.symm hvw]

/-- Rewiring preserves the trace, directly from the two rank-one contributions. -/
theorem rewire_trace_zero (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (Matrix.vecMulVec (edgeVector u w) (edgeVector u w) -
      Matrix.vecMulVec (edgeVector v w) (edgeVector v w)).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    (rewire_gram u v w huv huw hvw).1, (rewire_gram u v w huv huw hvw).2.1]
  norm_num

#print axioms lapMatrix_sup_of_disjoint
#print axioms lapMatrix_edge
#print axioms rewire_laplacian_difference
#print axioms edgeVector_dot
#print axioms rewire_gram
#print axioms rewire_trace_zero

end Gebendorfer.RadenkovicGutman
