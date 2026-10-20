import FormalConjectures.WrittenOnTheWallII.GraphConjecture404To407

/-! The corona is 2-dominating in every finite simple graph.
The exchange argument follows Gebendorfer's manuscript, revision R2,
linked in issue7267. OpenAI Codex assisted with formalization. -/

namespace CoronaTwoDominatingProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem corona_two_dominating [DecidableRel G.Adj] :
    ∀ v, v ∉ corona G → 2 ≤ (G.neighborFinset v ∩ corona G).card := by
  classical
  intro v hv
  obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
  have hImax : IsMaximumIndependent G I := ⟨hI.isIndepSet, hI.maximum⟩
  have hIC : ∀ w ∈ I, w ∈ corona G := by
    intro w hw
    simp only [corona, mem_filter, mem_univ, true_and]
    exact ⟨I, hImax, hw⟩
  have hvI : v ∉ I := fun h => hv (hIC v h)
  have hneighbor : ∃ u ∈ I, G.Adj v u := by
    by_contra! hn
    have hi : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
      intro a ha b hb hab
      by_cases hav : a = v
      · subst a
        by_cases hbv : b = v
        · exact (hab hbv.symm).elim
        · exact hn b ((mem_insert.mp hb).resolve_left hbv)
      · have haI : a ∈ I := (mem_insert.mp ha).resolve_left hav
        by_cases hbv : b = v
        · subst b
          exact fun h => hn a haI h.symm
        · exact hI.isIndepSet haI ((mem_insert.mp hb).resolve_left hbv) hab
    have hc := hI.maximum (insert v I) hi
    rw [card_insert_of_notMem hvI] at hc
    omega
  obtain ⟨u, hu, hvu⟩ := hneighbor
  by_contra hn
  have hcard : (G.neighborFinset v ∩ corona G).card ≤ 1 := by omega
  have huniq : ∀ w ∈ I, G.Adj v w → w = u := by
    intro w hw hvw
    apply card_le_one.mp hcard
    · exact mem_inter.mpr ⟨by simpa using hvw, hIC w hw⟩
    · exact mem_inter.mpr ⟨by simpa using hvu, hIC u hu⟩
  let J := insert v (I.erase u)
  have hJind : G.IsIndepSet (J : Set V) := by
    intro a ha b hb hab
    change a ∈ insert v (I.erase u) at ha
    change b ∈ insert v (I.erase u) at hb
    by_cases hav : a = v
    · subst a
      by_cases hbv : b = v
      · exact (hab hbv.symm).elim
      · have hbE : b ∈ I.erase u := (mem_insert.mp hb).resolve_left hbv
        intro hadj
        exact (ne_of_mem_erase hbE) (huniq b (mem_of_mem_erase hbE) hadj)
    · have haE : a ∈ I.erase u := (mem_insert.mp ha).resolve_left hav
      by_cases hbv : b = v
      · subst b
        intro hadj
        exact (ne_of_mem_erase haE) (huniq a (mem_of_mem_erase haE) hadj.symm)
      · exact hI.isIndepSet (mem_of_mem_erase haE)
          (mem_of_mem_erase ((mem_insert.mp hb).resolve_left hbv)) hab
  have hJcard : J.card = I.card := by
    have hpos : 0 < I.card := card_pos.mpr ⟨u, hu⟩
    dsimp [J]
    rw [card_insert_of_notMem (fun h => hvI (mem_of_mem_erase h)), card_erase_of_mem hu]
    omega
  have hJmax : IsMaximumIndependent G J := by
    refine ⟨hJind, ?_⟩
    intro K hK
    rw [hJcard]
    exact hI.maximum K hK
  apply hv
  simp only [corona, mem_filter, mem_univ, true_and]
  exact ⟨J, hJmax, mem_insert_self _ _⟩

end CoronaTwoDominatingProof

#print axioms CoronaTwoDominatingProof.corona_two_dominating
