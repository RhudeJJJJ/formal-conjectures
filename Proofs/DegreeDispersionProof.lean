import FormalConjectures.Arxiv.«2202.00325».DegreeDispersion

/-! Complete proofs of Clark Conjecture 2 and its star equality case.
The proof uses degrees in [1,n-1], the degree sum and a nonnegative square.
It is an alternative bounded-variance argument for Theorem 2.1 of
Gebendorfer's cited manuscript, rather than a line-by-line formalization of
its edge-pair defect identity. No claim about Conjecture 3 is made.
OpenAI Codex assisted with formalization. -/

namespace DegreeDispersionProof
open SimpleGraph Finset Clark.DegreeDispersion

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def slack : ℝ :=
  ∑ v : V, ((G.degree v : ℝ) - 1) * ((Fintype.card V : ℝ) - 1 - G.degree v)

theorem degree_sum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem slack_identity :
    slack G = 2 * (Fintype.card V : ℝ) * G.edgeFinset.card -
      (∑ v : V, (G.degree v : ℝ)^2) -
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
  have ht (v : V) : ((G.degree v : ℝ) - 1) *
      ((Fintype.card V : ℝ) - 1 - G.degree v) =
      (Fintype.card V : ℝ) * G.degree v - (G.degree v : ℝ)^2 -
        ((Fintype.card V : ℝ) - 1) := by ring
  simp only [slack, ht, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [degree_sum]
  ring

theorem defect_identity (hn : 2 ≤ Fintype.card V) (hm : 0 < G.edgeFinset.card) :
    ((Fintype.card V : ℝ) - 2)^2 / (4 * ((Fintype.card V : ℝ) - 1)) -
      dispersion G =
    (Fintype.card V : ℝ) * slack G / (4 * (G.edgeFinset.card : ℝ)^2) +
      (Fintype.card V : ℝ)^2 * ((G.edgeFinset.card : ℝ) - Fintype.card V + 1)^2 /
        (4 * (G.edgeFinset.card : ℝ)^2 * ((Fintype.card V : ℝ) - 1)) := by
  have hn' : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hm' : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [dispersion, slack_identity]
  field_simp [hn', hm']
  <;> ring

theorem degree_positive (hG : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ G.degree v := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have := hG.preconnected.degree_pos_of_nontrivial v
  omega

theorem edge_positive (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < G.edgeFinset.card := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  have hp := degree_positive G hG hn v
  have hb := G.degree_le_card_edgeFinset (v := v)
  omega

theorem slack_nonneg (hG : G.Connected) (hn : 2 ≤ Fintype.card V) : 0 ≤ slack G := by
  apply sum_nonneg
  intro v _
  have hp := degree_positive G hG hn v
  have hb := G.degree_lt_card_verts v
  have hp' : 0 ≤ (G.degree v : ℝ) - 1 := by exact_mod_cast (by omega : 1 ≤ G.degree v)
  have hb' : 0 ≤ (Fintype.card V : ℝ) - 1 - G.degree v := by
    have : (G.degree v : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast (by omega : G.degree v + 1 ≤ Fintype.card V)
    linarith
  exact mul_nonneg hp' hb'

theorem conjecture2 (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    dispersion G ≤ ((Fintype.card V : ℝ) - 2)^2 /
      (4 * ((Fintype.card V : ℝ) - 1)) := by
  have hid := defect_identity G hn (edge_positive G hG hn)
  have hs := slack_nonneg G hG hn
  have hnr : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hmr : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast edge_positive G hG hn
  have hdef : 0 ≤ ((Fintype.card V : ℝ) - 2)^2 / (4 * ((Fintype.card V : ℝ) - 1)) - dispersion G := by
    rw [hid]
    positivity
  linarith

end DegreeDispersionProof

#print axioms DegreeDispersionProof.conjecture2

