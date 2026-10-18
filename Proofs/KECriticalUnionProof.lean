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

/- The KE specialization of the corona theorem. The critical-set bridge is
credited to the literature in the source manuscript (revision R2).
OpenAI Codex assisted with formalization. -/

namespace KECriticalUnionProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture404To407

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma neighbor_mem {J : Finset V} {u v : V} (hu : u ∈ J) (huv : G.Adj u v) :
    v ∈ neighbors G J := by
  classical
  simp only [neighbors, mem_filter, mem_univ, true_and]
  exact ⟨u, hu, huv⟩

omit [DecidableRel G.Adj] in
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
          rw [Sym2.toFinset_mk_eq, insert_sdiff_of_mem _ hu,
            insert_sdiff_of_notMem _ hv]
          simp
        have hp : 1 ≤ (s(u,v).toFinset ∩ neighbors G J).card :=
          card_pos.mpr ⟨v, mem_inter.mpr ⟨by simp, hvN⟩⟩
        omega
    · by_cases hv : v ∈ J
      · have huN := neighbor_mem G hv huv.symm
        have hc : (s(u,v).toFinset \ J).card = 1 := by
          rw [Sym2.toFinset_mk_eq, insert_sdiff_of_notMem _ hu,
            insert_sdiff_of_mem _ hv]
          simp
        have hp : 1 ≤ (s(u,v).toFinset ∩ neighbors G J).card :=
          card_pos.mpr ⟨u, mem_inter.mpr ⟨by simp, huN⟩⟩
        omega
      · have hc : (s(u,v).toFinset \ J).card = 2 := by
          rw [Sym2.toFinset_mk_eq, insert_sdiff_of_notMem _ hu,
            insert_sdiff_of_notMem _ hv]
          simp [hne]
        omega

omit [DecidableRel G.Adj] in
lemma matching_weight_bound (J : Finset V) (M : G.Subgraph) [Fintype ↥M.edgeSet]
    (hM : M.IsMatching) :
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
        (mem_sdiff.mp hvE).1 (mem_sdiff.mp hvF).1
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

lemma matching_number_bound (J : Finset V) :
    2 * G.matchingNumber ≤ (Fintype.card V : ℝ) - J.card + (neighbors G J).card := by
  classical
  have hsup : G.matchingNumber ≤
      ((univ \ J).card + (neighbors G J).card : ℝ) / 2 := by
    unfold SimpleGraph.matchingNumber
    apply csSup_le
    · refine ⟨0, ⊥, ?_, ?_⟩
      · intro v hv
        simpa using hv
      · simp
    · rintro r ⟨M, hM, rfl⟩
      have hb := matching_weight_bound G J M hM
      have hr : 2 * (M.edgeSet.toFinset.card : ℝ) ≤
          (univ \ J).card + (neighbors G J).card := by exact_mod_cast hb
      linarith
  have hcard : ((univ \ J).card : ℝ) = Fintype.card V - J.card := by
    rw [card_sdiff_of_subset (subset_univ J), card_univ, Nat.cast_sub (card_le_univ J)]
  rw [hcard] at hsup
  linarith

lemma difference_bound (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V)
    (J : Finset V) : difference G J ≤ 2 * (G.indepNum : ℤ) - Fintype.card V := by
  have hb := matching_number_bound G J
  have hr : (J.card : ℝ) - (neighbors G J).card ≤
      2 * (G.indepNum : ℝ) - Fintype.card V := by linarith
  unfold difference
  exact_mod_cast hr

omit [DecidableRel G.Adj] in
lemma maximum_neighbors (I : Finset V) (hI : IsMaximumIndependent G I) :
    neighbors G I = univ \ I := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := (mem_filter.mp hv).2
    exact mem_sdiff.mpr ⟨mem_univ _, fun hvI => hI.1 hu hvI huv.ne huv⟩
  · intro hv
    have hvI := (mem_sdiff.mp hv).2
    by_contra hvN
    have hn : ∀ u ∈ I, ¬ G.Adj u v := by
      intro u hu huv
      exact hvN (neighbor_mem G hu huv)
    have hind : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
      intro a ha b hb hab
      by_cases hav : a = v
      · subst a
        by_cases hbv : b = v
        · exact (hab hbv.symm).elim
        · exact fun hvb => hn b ((mem_insert.mp hb).resolve_left hbv) hvb.symm
      · have haI := (mem_insert.mp ha).resolve_left hav
        by_cases hbv : b = v
        · subst b; exact hn a haI
        · exact hI.1 haI ((mem_insert.mp hb).resolve_left hbv) hab
    have hc := hI.2 (insert v I) hind
    rw [card_insert_of_notMem hvI] at hc
    omega

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma maximum_card (I : Finset V) (hI : IsMaximumIndependent G I) :
    I.card = G.indepNum := by
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  apply le_antisymm hI.1.card_le_indepNum
  rw [← hA.card_eq]
  exact hI.2 A hA.isIndepSet

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma maximum_difference (I : Finset V) (hI : IsMaximumIndependent G I) :
    difference G I = 2 * (G.indepNum : ℤ) - Fintype.card V := by
  classical
  unfold difference
  rw [maximum_neighbors G I hI, card_sdiff_of_subset (subset_univ I), card_univ,
    Nat.cast_sub (card_le_univ I), maximum_card G I hI]
  ring

lemma maximum_is_maximum_critical
    (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V)
    (I : Finset V) (hI : IsMaximumIndependent G I) : IsMaximumCriticalIndependent G I := by
  refine ⟨⟨hI.1, ?_⟩, ?_⟩
  · intro J _hJ
    rw [maximum_difference G I hI]
    exact difference_bound G hKE J
  · intro J hJ
    exact hI.2 J hJ.1

lemma maximum_critical_is_maximum
    (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V)
    (I : Finset V) (hI : IsMaximumCriticalIndependent G I) : IsMaximumIndependent G I := by
  obtain ⟨A, hA⟩ := G.maximumIndepSet_exists
  have hAm : IsMaximumIndependent G A := ⟨hA.isIndepSet, hA.maximum⟩
  have hAc := maximum_is_maximum_critical G hKE A hAm
  have hle := hI.2 A hAc.1
  exact ⟨hI.1.1, fun J hJ => (hA.maximum J hJ).trans hle⟩

lemma critical_union_eq_corona
    (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V) :
    criticalUnion G = corona G := by
  classical
  ext v
  simp only [criticalUnion, corona, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, maximum_critical_is_maximum G hKE I hI, hv⟩
  · rintro ⟨I, hI, hv⟩
    exact ⟨I, maximum_is_maximum_critical G hKE I hI, hv⟩

theorem critical_union_private_neighbors
    (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) = 0 := by
  classical
  have hEq := critical_union_eq_corona G hKE
  unfold privateExternalNeighborCount
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro v _ hv
  have hb := CoronaTwoDominatingProof.corona_two_dominating G v (by simpa [hEq] using hv.1)
  rw [← hEq, hv.2] at hb
  omega

#print axioms matching_number_bound
#print axioms difference_bound
#print axioms critical_union_eq_corona
#print axioms critical_union_private_neighbors
end KECriticalUnionProof
