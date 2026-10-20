import Proofs.SupportComponentBounds

/-! Both general corona strengthenings of WOWII 412a and 412b.
Source: Gebendorfer, Pendant-Support Inequalities for Graph Coronas, 2026.
-/
namespace WOWII412abBounds
open Finset SimpleGraph WOWII412dCore CoronaExchange PendantSupport SupportComponentBounds
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def degreeTwo : Finset V := by
  classical
  exact univ.filter (fun v => G.degree v = 2)

/-- The general corona residual-neighborhood bound. -/
theorem residual_bound :
    componentMaximum G (supports G) +
      (G.induce ((univ \ neighbors G (supports G) : Finset V) : Set V)).indepNum ≤
        (corona G).card := by
  classical
  let R := univ \ neighbors G (supports G)
  obtain ⟨D, hDR, hD, hcard⟩ := independent_on_exists G R
  have hDP : Disjoint D (leaves G) := by
    rw [Finset.disjoint_left]
    intro p hpD hp
    obtain ⟨s, hps, _⟩ := leaf_unique_neighbor G hp
    have hs := support_of_adj_leaf G hp hps
    exact (mem_sdiff.mp (hDR hpD)).2
      (mem_filter.mpr ⟨mem_univ _, s, hs, hps.symm⟩)
  have hsafe : ∀ s ∈ supports G, (∃ t ∈ supports G, G.Adj s t) →
      s ∉ D ∨ s ∈ corona G := by
    intro s _ ⟨t, ht, hst⟩
    refine Or.inl ?_
    intro hsD
    exact (mem_sdiff.mp (hDR hsD)).2 (mem_filter.mpr ⟨mem_univ _, t, ht, hst.symm⟩)
  have h := reserve_largest_component G D hD hDP hsafe
  rw [hcard] at h
  exact h

/-- A degree-two support adjacent to another support is in the corona. -/
lemma degree_two_support_mem_corona (hG : G.Connected) (horder : 2 < Fintype.card V)
    {s : V} (hs2 : s ∈ degreeTwo G) (hs : s ∈ supports G)
    (ht : ∃ t ∈ supports G, G.Adj s t) : s ∈ corona G := by
  classical
  obtain ⟨p, hp, hps⟩ : ∃ p ∈ leaves G, G.Adj p s := by
    simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using hs
  obtain ⟨t, ht, hst⟩ := ht
  obtain ⟨q, hq, hqt⟩ : ∃ q ∈ leaves G, G.Adj q t := by
    simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using ht
  have hqC := leaves_subset_corona G hq
  obtain ⟨M, hM, hqM⟩ : ∃ M : Finset V, Maximum G M ∧ q ∈ M := by
    simpa only [corona, mem_filter, mem_univ, true_and] using hqC
  have htM : t ∉ M := fun htM => hM.1 q hqM t htM hqt
  by_cases hsM : s ∈ M
  · exact maximum_subset_corona G M hM hsM
  · have hpM : p ∈ M := by
      by_contra hpM
      have hpn : p ∈ neighbors G M := by rw [maximum_neighbors G M hM]; simp [hpM]
      obtain ⟨x, hxM, hxp⟩ := (mem_filter.mp hpn).2
      obtain ⟨a, _ha, huniq⟩ := leaf_unique_neighbor G hp
      have hxs : x = s := (huniq x hxp.symm).trans (huniq s hps).symm
      exact hsM (hxs ▸ hxM)
    have hpt : p ≠ t := by
      intro he
      have hPT := independent_disjoint_neighbors G (leaves G) (leaves_independent G hG horder)
      exact Finset.disjoint_left.mp hPT hp (he ▸ ht)
    have hneighbors : G.neighborFinset s = {p, t} := by
      symm
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simpa using hps.symm
        · simpa using hst
      · rw [card_pair hpt, card_neighborFinset_eq_degree]
        exact (mem_filter.mp hs2).2.le
    have hswap := swap_maximum G M hM hsM hpM (fun x hxM hsx => by
      have hx : x ∈ ({p, t} : Finset V) := by rw [← hneighbors]; simpa using hsx
      rcases mem_insert.mp hx with hxp | hxt
      · exact hxp
      · exact False.elim (htM ((mem_singleton.mp hxt) ▸ hxM)))
    exact maximum_subset_corona G _ hswap (mem_insert_self _ _)

/-- The general corona degree-two bound. -/
theorem degree_two_bound (hG : G.Connected) (horder : 2 < Fintype.card V) :
    componentMaximum G (supports G) + (G.induce ((degreeTwo G) : Set V)).indepNum ≤
      (corona G).card := by
  classical
  obtain ⟨D, hD2, hD, hcard⟩ := independent_on_exists G (degreeTwo G)
  have hDP : Disjoint D (leaves G) := by
    rw [Finset.disjoint_left]
    intro p hpD hp
    have h2 : G.degree p = 2 := (mem_filter.mp (hD2 hpD)).2
    have h1 : G.degree p = 1 := (mem_filter.mp hp).2
    omega
  have hsafe : ∀ s ∈ supports G, (∃ t ∈ supports G, G.Adj s t) →
      s ∉ D ∨ s ∈ corona G := by
    intro s hs ht
    by_cases hsD : s ∈ D
    · exact Or.inr (degree_two_support_mem_corona G hG horder (hD2 hsD) hs ht)
    · exact Or.inl hsD
  have h := reserve_largest_component G D hD hDP hsafe
  rw [hcard] at h
  exact h

end WOWII412abBounds
