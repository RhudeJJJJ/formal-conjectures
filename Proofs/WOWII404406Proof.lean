import Proofs.WOWII405407Proof

/-!
# The remaining tree bounds WOWII 404 and 406

Source: Gebendorfer, The Corona of a Graph Is 2-Dominating, revision R2,
31 August 2026, Corollary 4.2. The zero private-neighbor theorem is reused.
The new steps verify that the integer right sides in rows 404 and 406 are
nonnegative. OpenAI Codex assisted with formalization and validation.
-/

namespace WOWII404406Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma leaf_neighbor_not_leaf (hG : G.Connected) (horder : 2 < Fintype.card V)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v) : G.degree v ≠ 1 := by
  intro hv
  obtain ⟨a, _ha, huniq_u⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
  obtain ⟨b, _hb, huniq_v⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  have hstep : ∀ {x y : V}, x = u ∨ x = v → G.Adj x y → y = u ∨ y = v := by
    intro x y hx hxy
    rcases hx with rfl | rfl
    · exact Or.inr ((huniq_u y hxy).trans (huniq_u v huv).symm)
    · exact Or.inl ((huniq_v y hxy).trans (huniq_v u huv.symm).symm)
  have hwalk : ∀ {x y : V}, G.Walk x y → x = u ∨ x = v → y = u ∨ y = v := by
    intro x y p
    induction p with
    | nil => exact id
    | cons hxy p ih => exact fun hx => ih (hstep hx hxy)
  have hall : ∀ x : V, x = u ∨ x = v := by
    intro x
    obtain ⟨p⟩ := hG u x
    exact hwalk p (Or.inl rfl)
  have hsub : (univ : Finset V) ⊆ {u, v} := by
    intro x _
    simpa only [mem_insert, mem_singleton] using hall x
  have hc := card_le_card hsub
  have hpair : ({u, v} : Finset V).card = 2 := card_pair huv.ne
  rw [card_univ, hpair] at hc
  omega

lemma leaves_card_ge_two (hT : G.IsTree) (horder : 2 < Fintype.card V) :
    2 ≤ (leaves G).card := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
  have hs : ({u, v} : Finset V) ⊆ leaves G := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [leaves, hu]
    · simp [leaves, hv]
  have hc := card_le_card hs
  simpa only [card_pair huv] using hc

omit [DecidableEq V] in
lemma supports_nonempty (hT : G.IsTree) (horder : 2 < Fintype.card V) :
    (supports G).Nonempty := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨v, huv, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
  refine ⟨v, ?_⟩
  simp only [supports, neighbors, mem_filter, mem_univ, true_and]
  exact ⟨u, by simp [leaves, hu], huv⟩

lemma private_nonleaves_eq_leaves (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (univ \ leaves G) = (leaves G).card := by
  classical
  unfold privateExternalNeighborCount
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    simpa only [mem_sdiff, mem_univ, true_and, not_not] using hv.1
  · intro hv
    have hdeg : G.degree v = 1 := (mem_filter.mp hv).2
    have hn : G.neighborFinset v ⊆ univ \ leaves G := by
      intro w hw
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro hwl
      exact leaf_neighbor_not_leaf G hG horder hdeg (by simpa using hw)
        ((mem_filter.mp hwl).2)
    refine ⟨by simpa only [mem_sdiff, mem_univ, true_and, not_not] using hv, ?_⟩
    rw [inter_eq_left.mpr hn, card_neighborFinset_eq_degree, hdeg]

theorem conjecture404 (hT : G.IsTree) (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      2 * ((supports G).card - (1 : ℤ)) := by
  have hs := card_pos.mpr (supports_nonempty G hT horder)
  rw [WOWII405407Proof.private_external_neighbors_eq_zero G hT.isBipartite]
  omega

theorem conjecture406 (hT : G.IsTree) (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      (privateExternalNeighborCount G (univ \ leaves G) : ℤ) - 2 := by
  have hl := leaves_card_ge_two G hT horder
  rw [WOWII405407Proof.private_external_neighbors_eq_zero G hT.isBipartite,
    private_nonleaves_eq_leaves G hT.connected horder]
  omega

end WOWII404406Proof

#print axioms WOWII404406Proof.conjecture404
#print axioms WOWII404406Proof.conjecture406
