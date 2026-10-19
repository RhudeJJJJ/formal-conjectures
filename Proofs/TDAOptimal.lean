import Proofs.TDABudget

/-! Attainment for the exact multiset annihilation number and finite minimum-sum subsets. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*}

/-- A submultiset of mapped distinct vertices is realized by a vertex subset.
The map itself need not be injective: degree multiplicities are preserved. -/
theorem lift_submultiset_map [DecidableEq V] (f : V → ℕ) (T : Finset V)
    (M : Multiset ℕ) (hM : M ≤ T.val.map f) :
    ∃ A : Finset V, A ⊆ T ∧ A.val.map f = M := by
  induction T using Finset.induction_on generalizing M with
  | empty =>
    have hz : M = 0 := by simpa using hM
    subst M
    exact ⟨∅, subset_refl _, rfl⟩
  | @insert a T ha IH =>
    have hm : M ≤ f a ::ₘ T.val.map f := by simpa [ha] using hM
    by_cases hf : f a ∈ M
    · have hres : M.erase (f a) ≤ T.val.map f := by
        simpa using Multiset.erase_le_erase (f a) hm
      obtain ⟨A, hAT, hmap⟩ := IH (M.erase (f a)) hres
      have haA : a ∉ A := fun h => ha (hAT h)
      refine ⟨insert a A, insert_subset (mem_insert_self _ _) (subset_insert_of_subset hAT), ?_⟩
      simpa [haA, hmap] using Multiset.cons_erase hf
    · obtain ⟨A, hAT, hmap⟩ := IH M ((Multiset.le_cons_of_notMem hf).mp hm)
      exact ⟨A, subset_insert_of_subset hAT, hmap⟩

/-- The supremum in the repository definition has an actual vertex-set witness. -/
theorem exists_annihilation_set [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A : Finset V, A.card = G.annihilationNumber ∧
      ∑ v ∈ A, G.degree v ≤ G.edgeFinset.card := by
  classical
  let F := (Finset.Iic G.degreeMultiset).filter (fun M => M.sum ≤ G.edgeFinset.card)
  have hF : F.Nonempty := ⟨0, by simp [F]⟩
  obtain ⟨M, hMF, heq⟩ := exists_mem_eq_sup F hF Multiset.card
  have hmem := mem_filter.mp hMF
  obtain ⟨A, _, hmap⟩ := lift_submultiset_map (fun v => G.degree v) univ M
    (mem_Iic.mp hmem.1)
  refine ⟨A, ?_, ?_⟩
  · have hcard := congrArg Multiset.card hmap
    simpa [SimpleGraph.annihilationNumber, F] using hcard.trans heq.symm
  · have hsum := congrArg Multiset.sum hmap
    simpa [← hsum] using hmem.2

/-- Among subsets of a prescribed size one can choose a minimum degree sum. -/
theorem exists_cheapest_subset [DecidableEq V] (S : Finset V) (d : V → ℕ)
    (t : ℕ) (ht : t ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ T.card = t ∧
      ∀ u ∈ T, ∀ v ∈ S \ T, d u ≤ d v := by
  classical
  let F := S.powerset.filter (fun T => T.card = t)
  have hF : F.Nonempty := by
    obtain ⟨T, hTS, hcard⟩ := exists_subset_card_eq ht
    exact ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hTS, hcard⟩⟩
  obtain ⟨T, hTF, hmin⟩ := exists_min_image F (fun T => ∑ v ∈ T, d v) hF
  have hTS := mem_powerset.mp (mem_filter.mp hTF).1
  have hcard := (mem_filter.mp hTF).2
  refine ⟨T, hTS, hcard, ?_⟩
  intro u hu v hv
  obtain ⟨hvS, hvT⟩ := mem_sdiff.mp hv
  have hvE : v ∉ T.erase u := fun h => hvT (mem_of_mem_erase h)
  let T' := insert v (T.erase u)
  have hT'S : T' ⊆ S := insert_subset hvS (subset_trans (erase_subset _ _) hTS)
  have hT'card : T'.card = t := by
    dsimp [T']
    rw [card_insert_of_notMem hvE, card_erase_of_mem hu, hcard]
    have hp : 0 < t := by rw [← hcard]; exact card_pos.mpr ⟨u, hu⟩
    omega
  have hT'F : T' ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hT'S, hT'card⟩
  have hsmall := hmin T' hT'F
  have hs := sum_erase_add T d hu
  have hs' : (∑ x ∈ T', d x) = d v + ∑ x ∈ T.erase u, d x := by
    dsimp [T']
    rw [sum_insert hvE]
  omega

open scoped Classical in
/-- The sum of the cheapest t entries is at most the corresponding fraction of
the whole sum, stated without division or rounding assumptions. -/
theorem exists_subset_average (S : Finset V) (d : V → ℕ) (t : ℕ) (ht : t ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ T.card = t ∧
      S.card * (∑ v ∈ T, d v) ≤ t * (∑ v ∈ S, d v) := by
  obtain ⟨T, hTS, hcard, horder⟩ := exists_cheapest_subset S d t ht
  have hpairs : (S \ T).card * (∑ u ∈ T, d u) ≤ T.card * (∑ v ∈ S \ T, d v) := by
    calc
      _ = ∑ u ∈ T, ∑ _v ∈ S \ T, d u := by simp [sum_mul, Nat.mul_comm]
      _ ≤ ∑ _u ∈ T, ∑ v ∈ S \ T, d v :=
        sum_le_sum fun u hu => sum_le_sum fun v hv => horder u hu v hv
      _ = _ := by simp
  have hsum := sum_sdiff hTS (f := d)
  have hcards := card_sdiff_add_card_eq_card hTS
  refine ⟨T, hTS, hcard, ?_⟩
  rw [← hsum, ← hcards, ← hcard]
  nlinarith

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.exists_annihilation_set
#print axioms TotalDominationAnnihilationProof.exists_subset_average
#print axioms TotalDominationAnnihilationProof.lift_submultiset_map
#print axioms TotalDominationAnnihilationProof.exists_cheapest_subset
#print axioms Finset.exists_mem_eq_sup
