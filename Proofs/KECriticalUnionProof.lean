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

/-! The KE specialization of the corona theorem. The critical-set bridge is
credited to the literature in the source manuscript (revision R2).
OpenAI Codex assisted with formalization. -/

namespace KECriticalUnionProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma neighbor_mem {J : Finset V} {u v : V} (hu : u ∈ J) (huv : G.Adj u v) :
    v ∈ neighbors G J := by
  classical
  simp only [neighbors, mem_filter, mem_univ, true_and]
  exact ⟨u, hu, huv⟩

lemma edge_weight (J : Finset V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    2 ≤ (e.toFinset \ J).card + (e.toFinset ∩ neighbors G J).card := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := he
    have hne : u ≠ v := huv.ne
    by_cases hu : u ∈ J
    · have hvN := neighbor_mem G hu huv
      by_cases hv : v ∈ J
      · have huN := neighbor_mem G hv huv.symm
        have hcard : (s(u,v).toFinset ∩ neighbors G J).card = 2 := by
          simp [Sym2.toFinset_mk_eq, huN, hvN, hne]
        omega
      · have hc : (s(u,v).toFinset \ J).card = 1 := by
          simp [Sym2.toFinset_mk_eq, hu, hv]
        have hp : 1 ≤ (s(u,v).toFinset ∩ neighbors G J).card :=
          card_pos.mpr ⟨v, mem_inter.mpr ⟨by simp, hvN⟩⟩
        omega
    · by_cases hv : v ∈ J
      · have huN := neighbor_mem G hv huv.symm
        have hc : (s(u,v).toFinset \ J).card = 1 := by
          simp [Sym2.toFinset_mk_eq, hu, hv]
        have hp : 1 ≤ (s(u,v).toFinset ∩ neighbors G J).card :=
          card_pos.mpr ⟨u, mem_inter.mpr ⟨by simp, huN⟩⟩
        omega
      · have hc : (s(u,v).toFinset \ J).card = 2 := by
          simp [Sym2.toFinset_mk_eq, hu, hv, hne]
        omega

lemma matching_weight_bound (J : Finset V) (M : G.Subgraph) (hM : M.IsMatching) :
    2 * M.edgeSet.toFinset.card ≤ (univ \ J).card + (neighbors G J).card := by
  classical
  let E := M.edgeSet.toFinset
  have hdisj : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e.toFinset f.toFinset := by
    intro e he f hf hef
    rw [Set.mem_toFinset] at he hf
    apply Finset.disjoint_left.mpr
    intro x hxe hxf
    rw [Sym2.mem_toFinset] at hxe hxf
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxf
    rw [Subgraph.mem_edgeSet] at he hf
    apply hef
    rw [hM.eq_of_adj_left he hf]
  have hA : (∑ e ∈ E, (e.toFinset \ J).card) ≤ (univ \ J).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro v hv
      obtain ⟨e, _, he⟩ := mem_biUnion.mp hv
      exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp he).2⟩
    · intro e he f hf hef
      apply Finset.disjoint_left.mpr
      intro v hvE hvF
      exact Finset.disjoint_left.mp (hdisj e he f hf hef)
        (mem_of_mem_sdiff hvE) (mem_of_mem_sdiff hvF)
  have hB : (∑ e ∈ E, (e.toFinset ∩ neighbors G J).card) ≤ (neighbors G J).card := by
    rw [← card_biUnion]
    · apply card_le_card
      intro v hv
      obtain ⟨e, _, he⟩ := mem_biUnion.mp hv
      exact (mem_inter.mp he).2
    · intro e he f hf hef
      apply Finset.disjoint_left.mpr
      intro v hvE hvF
      exact Finset.disjoint_left.mp (hdisj e he f hf hef)
        (mem_inter.mp hvE).1 (mem_inter.mp hvF).1
  have hc : ∑ e ∈ E, 2 ≤ ∑ e ∈ E,
      ((e.toFinset \ J).card + (e.toFinset ∩ neighbors G J).card) := by
    apply sum_le_sum
    intro e he
    exact edge_weight G J e (M.edgeSet_subset (Set.mem_toFinset.mp he))
  simp only [sum_const, smul_eq_mul, sum_add_distrib] at hc
  change 2 * E.card ≤ _
  omega

#print axioms edge_weight
#print axioms matching_weight_bound
end KECriticalUnionProof

