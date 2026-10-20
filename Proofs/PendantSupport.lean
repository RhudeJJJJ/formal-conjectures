import Proofs.CoronaExchange
import Proofs.WOWII412dAssembly

/-! Pendant/support and induced-invariant helpers for WOWII 412a/b/e.
The adjacent-leaf exclusion is reused from the completed 404/406 certificate.
-/
namespace PendantSupport
open Finset SimpleGraph WOWII412dCore CoronaExchange
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
lemma degree_nat_card (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  rw [← G.card_neighborSet_eq_degree v, Nat.card_eq_fintype_card]

noncomputable def leaves : Finset V := by
  classical
  exact univ.filter (fun v => G.degree v = 1)
noncomputable def supports : Finset V := neighbors G (leaves G)

lemma leaf_neighbor_not_leaf [DecidableRel G.Adj] (hG : G.Connected) (horder : 2 < Fintype.card V)
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


omit [DecidableEq V] in
lemma leaf_unique_neighbor {p : V} (hp : p ∈ leaves G) :
    ∃ s, G.Adj p s ∧ ∀ w, G.Adj p w → w = s := by
  classical
  exact degree_eq_one_iff_existsUnique_adj.mp ((mem_filter.mp hp).2)

lemma leaves_independent (hG : G.Connected) (horder : 2 < Fintype.card V) :
    Independent G (leaves G) := by
  classical
  intro u hu v hv huv
  exact leaf_neighbor_not_leaf G hG horder ((mem_filter.mp hu).2) huv ((mem_filter.mp hv).2)

lemma leaves_subset_corona : leaves G ⊆ corona G := by
  classical
  intro p hp
  exact leaf_mem_corona G ((mem_filter.mp hp).2)

omit [DecidableEq V] in
lemma support_of_adj_leaf {p s : V} (hp : p ∈ leaves G) (hps : G.Adj p s) :
    s ∈ supports G := by
  classical
  exact mem_filter.mpr ⟨mem_univ _, p, hp, hps⟩

lemma indepNum_le_corona : G.indepNum ≤ (corona G).card := by
  obtain ⟨M, hM⟩ := exists_maximum G
  have he : M.card = G.indepNum := G.maximumIndepSet_card_eq_indepNum M
    ⟨(independent_iff G M).mp hM.1, fun J hJ => hM.2 J ((independent_iff G J).mpr hJ)⟩
  rw [← he]
  exact card_le_card (maximum_subset_corona G M hM)

omit [DecidableEq V] in
lemma independent_card_le_indepNum (D : Finset V) (hD : Independent G D) :
    D.card ≤ G.indepNum := ((independent_iff G D).mp hD).card_le_indepNum

lemma independent_on_exists (A : Finset V) :
    ∃ D : Finset V, D ⊆ A ∧ Independent G D ∧
      D.card = (G.induce (A : Set V)).indepNum := by
  classical
  obtain ⟨J, hJ⟩ := exists_maximum (G.induce (A : Set V))
  let D := J.image Subtype.val
  refine ⟨D, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact i.property
  · intro u hu v hv huv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    exact hJ.1 i hi j hj huv
  · rw [card_image_of_injective _ Subtype.val_injective]
    exact (G.induce (A : Set V)).maximumIndepSet_card_eq_indepNum J
      ⟨(independent_iff _ J).mp hJ.1,
        fun K hK => hJ.2 K ((independent_iff _ K).mpr hK)⟩

lemma induced_degree_eq [DecidableRel G.Adj] (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v = (G.neighborFinset v.val ∩ A).card := by
  classical
  have h : ((G.induce (A : Set V)).neighborFinset v).image Subtype.val =
      G.neighborFinset v.val ∩ A := by
    ext w
    simp
  rw [← card_neighborFinset_eq_degree, ← h, card_image_of_injective _ Subtype.val_injective]

lemma bipartite_indepNum_ge_two (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    2 ≤ G.indepNum := by
  classical
  obtain ⟨A, hA⟩ := exists_bipartition G hb
  have ha := independent_card_le_indepNum G A hA.1
  have hb := independent_card_le_indepNum G (univ \ A) hA.2
  have hc := card_sdiff_add_card_eq_card (subset_univ A)
  rw [card_univ] at hc
  omega

end PendantSupport
