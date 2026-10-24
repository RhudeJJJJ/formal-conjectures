module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Graph-to-matrix bridge for the arbitrary-core determinant quotient.
-/
public import Proofs.RGModernRadenkovicGutmanCoreQuotient
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Aesop

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Gebendorfer.RadenkovicGutman.CoreQuotient

open Matrix Finset
open scoped Classical
noncomputable section

attribute [-instance] SimpleGraph.instLocallyFiniteSumSumOfDecidableEq

variable {V W X : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
variable {K : Type*} [Field K]

/-- Graph union gives Laplacian addition when the edge sets are disjoint. -/
theorem lapMatrix_sup_of_disjoint (G H : SimpleGraph V)
    (h : Disjoint G H) :
    (G ⊔ H).lapMatrix K = G.lapMatrix K + H.lapMatrix K := by
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

/-- A single edge contributes exactly its incidence-vector outer product. -/
theorem lapMatrix_edge (u w : V) (huw : u ≠ w) :
    (SimpleGraph.edge u w).lapMatrix K =
      Matrix.vecMulVec (incidence u w) (incidence u w) := by
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
    incidence]
  rw [hd i]
  clear hd hnu hnw hno
  by_cases hiu : i = u <;> by_cases hiw : i = w <;>
    by_cases hju : j = u <;> by_cases hjw : j = w <;>
      simp_all [SimpleGraph.edge_adj] <;> aesop


theorem lapMatrix_sum (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).lapMatrix K = fromBlocks (G.lapMatrix K) 0 0 (H.lapMatrix K) := by
  have hdl (i : V) : (G ⊕g H).degree (.inl i) = G.degree i := by
    calc
      _ = ∑ j : V ⊕ W, if (G ⊕g H).Adj (.inl i) j then 1 else 0 := by
        simpa only [Nat.cast_id] using (G ⊕g H).degree_eq_sum_if_adj (R := ℕ) (.inl i)
      _ = ∑ j : V, if G.Adj i j then 1 else 0 := by
        rw [Fintype.sum_sum_type]
        simp
      _ = _ := by simpa only [Nat.cast_id] using (G.degree_eq_sum_if_adj (R := ℕ) i).symm
  have hdr (i : W) : (G ⊕g H).degree (.inr i) = H.degree i := by
    calc
      _ = ∑ j : V ⊕ W, if (G ⊕g H).Adj (.inr i) j then 1 else 0 := by
        simpa only [Nat.cast_id] using (G ⊕g H).degree_eq_sum_if_adj (R := ℕ) (.inr i)
      _ = ∑ j : W, if H.Adj i j then 1 else 0 := by
        rw [Fintype.sum_sum_type]
        simp
      _ = _ := by simpa only [Nat.cast_id] using (H.degree_eq_sum_if_adj (R := ℕ) i).symm
  ext (i | i) (j | j) <;>
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
      Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      hdl, hdr, if_false, Matrix.zero_apply] <;> simp [SimpleGraph.sum]

def shifted (z : K) (G : SimpleGraph V) : Matrix V V K :=
  z • 1 - G.lapMatrix K

theorem shifted_sum (z : K) (G : SimpleGraph V) (H : SimpleGraph W) :
    shifted z (G ⊕g H) = fromBlocks (shifted z G) 0 0 (shifted z H) := by
  rw [shifted, lapMatrix_sum]
  ext (i | i) (j | j) <;> simp [shifted, Matrix.fromBlocks, Matrix.one_apply]

/-- Add one root edge between two otherwise disjoint graphs. -/
def join (G : SimpleGraph V) (H : SimpleGraph W) (u : V) (v : W) :
    SimpleGraph (V ⊕ W) :=
  (G ⊕g H) ⊔ SimpleGraph.edge (.inl u) (.inr v)

theorem shifted_join (z : K) (G : SimpleGraph V) (H : SimpleGraph W)
    (u : V) (v : W) :
    shifted z (join G H u v) = fromBlocks (shifted z G) 0 0 (shifted z H) -
      vecMulVec (incidence (.inl u) (.inr v)) (incidence (.inl u) (.inr v)) := by
  have hd : Disjoint (G ⊕g H) (SimpleGraph.edge (.inl u) (.inr v)) := by
    apply (SimpleGraph.disjoint_edge _).mpr
    simp [SimpleGraph.sum]
  have hl : ((G ⊕g H) ⊔ SimpleGraph.edge (.inl u) (.inr v)).lapMatrix K =
      (G ⊕g H).lapMatrix K + (SimpleGraph.edge (.inl u) (.inr v)).lapMatrix K := by
    convert lapMatrix_sup_of_disjoint (K := K) _ _ hd using 1 <;> congr 3
  calc
    _ = z • (1 : Matrix (V ⊕ W) (V ⊕ W) K) -
        ((G ⊕g H).lapMatrix K + (SimpleGraph.edge (.inl u) (.inr v)).lapMatrix K) := by
      unfold join shifted
      convert congrArg (fun A : Matrix (V ⊕ W) (V ⊕ W) K => z • 1 - A) hl using 1; congr 3
    _ = _ := by
      rw [lapMatrix_edge (K := K) _ _ (by simp), ← sub_sub, ← shifted, shifted_sum]

def joinTwo (G : SimpleGraph V) (P : SimpleGraph W) (Q : SimpleGraph X)
    (u : V) (v : W) (w : X) : SimpleGraph (V ⊕ W ⊕ X) :=
  ((G ⊕g (P ⊕g Q)) ⊔ SimpleGraph.edge (.inl u) (.inr (.inl v))) ⊔
    SimpleGraph.edge (.inl u) (.inr (.inr w))

theorem shifted_joinTwo (z : K) (G : SimpleGraph V)
    (P : SimpleGraph W) (Q : SimpleGraph X) (u : V) (v : W) (w : X) :
    shifted z (joinTwo G P Q u v w) =
      forestMatrix (shifted z G) (shifted z P) (shifted z Q) -
      vecMulVec (incidence (.inl u) (.inr (.inl v)))
        (incidence (.inl u) (.inr (.inl v))) -
      vecMulVec (incidence (.inl u) (.inr (.inr w)))
        (incidence (.inl u) (.inr (.inr w))) := by
  have hd : Disjoint (G ⊕g (P ⊕g Q))
      (SimpleGraph.edge (.inl u) (.inr (.inl v))) := by
    apply (SimpleGraph.disjoint_edge _).mpr
    simp [SimpleGraph.sum]
  have he : Disjoint ((G ⊕g (P ⊕g Q)) ⊔
      SimpleGraph.edge (.inl u) (.inr (.inl v)))
      (SimpleGraph.edge (.inl u) (.inr (.inr w))) := by
    apply (SimpleGraph.disjoint_edge _).mpr
    simp [SimpleGraph.sum, SimpleGraph.edge_adj]
  have hl : (((G ⊕g (P ⊕g Q)) ⊔ SimpleGraph.edge (.inl u) (.inr (.inl v))) ⊔
      SimpleGraph.edge (.inl u) (.inr (.inr w))).lapMatrix K =
      ((G ⊕g (P ⊕g Q)) ⊔ SimpleGraph.edge (.inl u) (.inr (.inl v))).lapMatrix K +
      (SimpleGraph.edge (.inl u) (.inr (.inr w))).lapMatrix K := by
    convert lapMatrix_sup_of_disjoint (K := K) _ _ he using 1 <;> congr 3
  have hm : ((G ⊕g (P ⊕g Q)) ⊔ SimpleGraph.edge (.inl u) (.inr (.inl v))).lapMatrix K =
      (G ⊕g (P ⊕g Q)).lapMatrix K +
      (SimpleGraph.edge (.inl u) (.inr (.inl v))).lapMatrix K := by
    convert lapMatrix_sup_of_disjoint (K := K) _ _ hd using 1 <;> congr 3
  unfold joinTwo shifted
  rw [hl, hm,
    lapMatrix_edge (K := K) _ _ (by simp), lapMatrix_edge (K := K) _ _ (by simp)]
  rw [← sub_sub, ← sub_sub, ← shifted, shifted_sum, shifted_sum]
  rfl

#print axioms shifted_join
#print axioms shifted_joinTwo

attribute [instance] SimpleGraph.instLocallyFiniteSumSumOfDecidableEq

end
end Gebendorfer.RadenkovicGutman.CoreQuotient
