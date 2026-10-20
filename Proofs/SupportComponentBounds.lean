import Proofs.PendantSupport

/-! Reserve one pendant for each support in a connected component.
Source: Gebendorfer, Pendant-Support Inequalities for Graph Coronas, 2026.
The cardinality reservation lemma avoids constructing a Hall matching. -/
namespace SupportComponentBounds
open Finset SimpleGraph WOWII412dCore CoronaExchange PendantSupport
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def componentVertices (S : Finset V)
    (c : (G.induce (S : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image Subtype.val

omit [Fintype V] in
lemma component_subset (S : Finset V) (c : (G.induce (S : Set V)).ConnectedComponent) :
    componentVertices G S c ⊆ S := by
  classical
  intro v hv
  obtain ⟨i, _, rfl⟩ := mem_image.mp hv
  exact i.property

omit [Fintype V] in
lemma component_card (S : Finset V) (c : (G.induce (S : Set V)).ConnectedComponent) :
    (componentVertices G S c).card = Nat.card c.supp := by
  classical
  rw [componentVertices, card_image_of_injective _ Subtype.val_injective,
    Nat.card_eq_card_toFinset]

omit [Fintype V] in
lemma component_has_neighbor (S : Finset V)
    (c : (G.induce (S : Set V)).ConnectedComponent)
    (hc : 2 ≤ (componentVertices G S c).card) {s : V}
    (hs : s ∈ componentVertices G S c) : ∃ t ∈ S, G.Adj s t := by
  classical
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
  have hex : ∃ t ∈ componentVertices G S c, t ≠ i.val := by
    by_contra! hn
    have hsub : componentVertices G S c ⊆ {i.val} := by
      intro t ht
      exact mem_singleton.mpr (hn t ht)
    have hcard := card_le_card hsub
    simp only [card_singleton] at hcard
    omega
  obtain ⟨t, ht, hti⟩ := hex
  obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
  have hij : i ≠ j := fun he => hti (congrArg Subtype.val he.symm)
  obtain ⟨w, hiw⟩ := (c.reachable_of_mem_supp (by simpa using hi) (by simpa using hj)).nonempty_neighborSet_left hij
  exact ⟨w.val, w.property, hiw⟩

lemma select_leaves (C : Finset V) (hC : C ⊆ supports G) :
    ∃ L : Finset V, L ⊆ leaves G ∧ L.card = C.card ∧
      ∀ p ∈ L, ∃ s ∈ C, G.Adj p s := by
  classical
  have hex : ∀ s : {s // s ∈ C}, ∃ p ∈ leaves G, G.Adj p s.val := by
    intro s
    have hs := hC s.property
    simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using hs
  choose pick hp hps using hex
  have hinj : Function.Injective pick := by
    intro s t he
    obtain ⟨a, _ha, huniq⟩ := leaf_unique_neighbor G (hp s)
    apply Subtype.ext
    exact (huniq s.val (hps s)).trans (huniq t.val (he ▸ hps t)).symm
  refine ⟨C.attach.image pick, ?_, ?_, ?_⟩
  · intro p hpL
    obtain ⟨s, _, rfl⟩ := mem_image.mp hpL
    exact hp s
  · rw [card_image_of_injective _ hinj, card_attach]
  · intro p hpL
    obtain ⟨s, _, rfl⟩ := mem_image.mp hpL
    exact ⟨s.val, s.property, hps s⟩

/-- A component can reserve its chosen pendants if its nonisolated supports
are absent from the independent set or already belong to the corona. -/
lemma reserve_component (D : Finset V) (hD : Independent G D)
    (hDP : Disjoint D (leaves G))
    (hsafe : ∀ s ∈ supports G, (∃ t ∈ supports G, G.Adj s t) → s ∉ D ∨ s ∈ corona G)
    (c : (G.induce ((supports G) : Set V)).ConnectedComponent) :
    Nat.card c.supp + D.card ≤ (corona G).card := by
  classical
  let C := componentVertices G (supports G) c
  have hCS : C ⊆ supports G := component_subset G _ c
  obtain ⟨L, hLP, hLC, hL⟩ := select_leaves G C hCS
  have hLcorona := hLP.trans (leaves_subset_corona G)
  have hDL := hDP.mono_right hLP
  have hcase : L.card ≤ 1 ∨ ∀ x ∈ D \ corona G, ∀ p ∈ L, ¬ G.Adj x p := by
    by_cases hsmall : C.card ≤ 1
    · exact Or.inl (hLC ▸ hsmall)
    · refine Or.inr ?_
      intro x hx p hp hxp
      obtain ⟨s, hs, hps⟩ := hL p hp
      obtain ⟨a, _ha, huniq⟩ := leaf_unique_neighbor G (hLP hp)
      have hxs : x = s := (huniq x hxp.symm).trans (huniq s hps).symm
      subst x
      have hge : 2 ≤ (componentVertices G (supports G) c).card := by
        change 2 ≤ C.card
        omega
      rcases hsafe s (hCS hs) (component_has_neighbor G _ c hge hs) with hn | hc
      · exact hn (mem_sdiff.mp hx).1
      · exact (mem_sdiff.mp hx).2 hc
  have hb := reserved_cardinality G D L hD hLcorona hDL hcase
  have hc : C.card = Nat.card c.supp := component_card G _ c
  omega

noncomputable def componentMaximum (S : Finset V) : ℕ :=
  sSup (Set.range fun c : (G.induce (S : Set V)).ConnectedComponent => Nat.card c.supp)

lemma reserve_largest_component (D : Finset V) (hD : Independent G D)
    (hDP : Disjoint D (leaves G))
    (hsafe : ∀ s ∈ supports G, (∃ t ∈ supports G, G.Adj s t) → s ∉ D ∨ s ∈ corona G) :
    componentMaximum G (supports G) + D.card ≤ (corona G).card := by
  have hDcard := independent_card_le_corona G D hD
  have hc : componentMaximum G (supports G) ≤ (corona G).card - D.card := by
    apply csSup_le'
    rintro _ ⟨c, rfl⟩
    change Nat.card c.supp ≤ _
    have h := reserve_component G D hD hDP hsafe c
    omega
  omega

end SupportComponentBounds
