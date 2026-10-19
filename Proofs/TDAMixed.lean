import Proofs.TDAMixedBase

/-! The weighted transversal bound for indexed edges of sizes one to three. -/

namespace TotalDominationAnnihilationProof.Hypergraph
open Finset

variable {V I : Type*} [DecidableEq V]

private theorem mixed_cover_aux (n : ℕ) :
    ∀ (U : Finset V) (J : Finset I) (edge : I → Finset V),
      potential U J edge ≤ n → (∀ i ∈ J, edge i ⊆ U) →
      (∀ i ∈ J, 1 ≤ (edge i).card ∧ (edge i).card ≤ 3) →
      ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧ 6 * D.card ≤ potential U J edge := by
  classical
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro U J edge hn hsub hrank
    by_cases hhigh : ∃ v ∈ U, 4 ≤ incidentWeight J edge v
    · obtain ⟨v, hv, hw⟩ := hhigh
      let K := J \ incident J edge v
      let U' := U.erase v
      have hdrop := potential_strong_delete U J edge hv
      have hstrict : potential U' K edge < n := by
        change potential U' K edge + 2 + incidentWeight J edge v =
          potential U J edge at hdrop
        omega
      have hsub' : ∀ i ∈ K, edge i ⊆ U' := by
        intro i hi w hw'
        obtain ⟨hiJ, hiv⟩ := mem_sdiff.mp hi
        refine mem_erase.mpr ⟨?_, hsub i hiJ hw'⟩
        intro hwv
        subst w
        exact hiv (mem_incident.mpr ⟨hiJ, hw'⟩)
      have hrank' : ∀ i ∈ K, 1 ≤ (edge i).card ∧ (edge i).card ≤ 3 := by
        intro i hi
        exact hrank i (mem_sdiff.mp hi).1
      obtain ⟨D, hDU, hDhit, hDb⟩ :=
        IH (potential U' K edge) hstrict U' K edge le_rfl hsub' hrank'
      have hvD : v ∉ D := by
        intro hvD
        exact (mem_erase.mp (hDU hvD)).1 rfl
      refine ⟨insert v D, insert_subset hv (subset_trans hDU (erase_subset _ _)), ?_, ?_⟩
      · intro i hi
        by_cases hvi : v ∈ edge i
        · exact ⟨v, mem_insert_self _ _, hvi⟩
        · have hiK : i ∈ K := mem_sdiff.mpr ⟨hi, fun h => hvi (mem_incident.mp h).2⟩
          obtain ⟨w, hwD, hwi⟩ := hDhit i hiK
          exact ⟨w, mem_insert_of_mem hwD, hwi⟩
      · rw [card_insert_of_notMem hvD]
        change potential U' K edge + 2 + incidentWeight J edge v =
          potential U J edge at hdrop
        omega
    · have hlow : ∀ v ∈ U, incidentWeight J edge v ≤ 3 := by
        intro v hv
        by_contra hbad
        exact hhigh ⟨v, hv, by omega⟩
      by_cases htwo : ∃ i ∈ J, (edge i).card = 2
      · obtain ⟨i, hi, hsize⟩ := htwo
        obtain ⟨u, v, huv, heq, horient⟩ := orient_two_edge J edge hsize
        have hui : u ∈ edge i := by rw [heq]; simp
        have hvi : v ∈ edge i := by rw [heq]; simp
        have hu : u ∈ U := hsub i hi hui
        have hv : v ∈ U := hsub i hi hvi
        let K := J \ incident J edge u
        let U' := (U.erase u).erase v
        let edge' := fun j => (edge j).erase v
        have hthree : ∀ j ∈ K, v ∈ edge j → (edge j).card = 3 := by
          intro j hj hvj
          obtain ⟨hjJ, hju⟩ := mem_sdiff.mp hj
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hju (mem_incident.mpr ⟨hi, hui⟩)
          exact other_edge_is_three J edge hi hjJ hvi hvj hij hsize
            (hrank j hjJ) (hlow v hv)
        have hdeg := incident_card_le_two_of_two_edge J edge hi hvi hsize (hlow v hv)
        have hdrop := two_edge_potential_drop U J edge hi hu hv huv hui hvi hsize
          hdeg horient hthree
        change potential U' K edge' + 6 ≤ potential U J edge at hdrop
        have hstrict : potential U' K edge' < n := by omega
        have hsub' : ∀ j ∈ K, edge' j ⊆ U' := by
          intro j hj w hw
          obtain ⟨hwv, hwe⟩ := mem_erase.mp hw
          obtain ⟨hjJ, hju⟩ := mem_sdiff.mp hj
          refine mem_erase.mpr ⟨hwv, mem_erase.mpr ⟨?_, hsub j hjJ hwe⟩⟩
          intro hwu
          subst w
          exact hju (mem_incident.mpr ⟨hjJ, hwe⟩)
        have hrank' : ∀ j ∈ K, 1 ≤ (edge' j).card ∧ (edge' j).card ≤ 3 := by
          intro j hj
          obtain ⟨hjJ, _⟩ := mem_sdiff.mp hj
          by_cases hvj : v ∈ edge j
          · have hs := hthree j hj hvj
            dsimp [edge']
            rw [card_erase_of_mem hvj, hs]
            omega
          · simpa only [edge', erase_eq_of_notMem hvj] using hrank j hjJ
        obtain ⟨D, hDU, hDhit, hDb⟩ :=
          IH (potential U' K edge') hstrict U' K edge' le_rfl hsub' hrank'
        have hDU' : D ⊆ U := subset_trans hDU
          (subset_trans (erase_subset _ _) (erase_subset _ _))
        have huD : u ∉ D := by
          intro huD
          exact (mem_erase.mp (mem_erase.mp (hDU huD)).2).1 rfl
        refine ⟨insert u D, insert_subset hu hDU', ?_, ?_⟩
        · intro j hj
          by_cases huj : u ∈ edge j
          · exact ⟨u, mem_insert_self _ _, huj⟩
          · have hjK : j ∈ K := mem_sdiff.mpr ⟨hj, fun h => huj (mem_incident.mp h).2⟩
            obtain ⟨w, hwD, hwj⟩ := hDhit j hjK
            exact ⟨w, mem_insert_of_mem hwD, (mem_erase.mp hwj).2⟩
        · rw [card_insert_of_notMem huD]
          omega
      · have hthree : ∀ i ∈ J, (edge i).card = 3 := by
          intro i hi
          have hr := hrank i hi
          have hne2 : (edge i).card ≠ 2 := fun h => htwo ⟨i, hi, h⟩
          have hne1 : (edge i).card ≠ 1 := by
            intro hone
            obtain ⟨v, hvi⟩ := card_pos.mp (by omega : 0 < (edge i).card)
            have hw := weight_le_incidentWeight J edge hi hvi
            rw [hone, edgeWeight_one] at hw
            have hl := hlow v (hsub i hi hvi)
            omega
          omega
        have hdeg : ∀ v ∈ U, (incident J edge v).card ≤ 3 := by
          intro v hv
          rw [← incidentWeight_eq_card J edge hthree v]
          exact hlow v hv
        have hinc := sum_incident_card U J edge hsub
        have hrows : (∑ i ∈ J, (edge i).card) = 3 * J.card := by
          rw [sum_congr rfl hthree]
          simp [Nat.mul_comm]
        have hsum : (∑ v ∈ U, (incident J edge v).card) ≤ 3 * U.card := by
          calc
            _ ≤ ∑ _v ∈ U, (3 : ℕ) := sum_le_sum hdeg
            _ = _ := by simp [Nat.mul_comm]
        have hmn : J.card ≤ U.card := by omega
        have hpot : potential U J edge = 2 * U.card + J.card := by
          unfold potential
          have hw : (∑ i ∈ J, edgeWeight (edge i).card) = J.card := by
            calc
              _ = ∑ _i ∈ J, (1 : ℕ) := sum_congr rfl (fun i hi => by rw [hthree i hi]; rfl)
              _ = _ := by simp
          rw [hw]
        obtain ⟨D, hDU, hDhit, hDb⟩ := three_uniform_cover U J edge hsub hthree
        exact ⟨D, hDU, hDhit, by rw [hpot]; omega⟩

/-- Mixed transversal bound, retaining all edge indices and multiplicities. -/
theorem mixed_cover (U : Finset V) (J : Finset I) (edge : I → Finset V)
    (hsub : ∀ i ∈ J, edge i ⊆ U)
    (hrank : ∀ i ∈ J, 1 ≤ (edge i).card ∧ (edge i).card ≤ 3) :
    ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧ 6 * D.card ≤ potential U J edge :=
  mixed_cover_aux (potential U J edge) U J edge le_rfl hsub hrank

open scoped Classical in
/-- The two/three-edge specialization, with the number of indexed two-edges explicit. -/
theorem mixed_cover_two_three (U : Finset V) (J : Finset I) (edge : I → Finset V)
    (hsub : ∀ i ∈ J, edge i ⊆ U)
    (hrank : ∀ i ∈ J, 2 ≤ (edge i).card ∧ (edge i).card ≤ 3) :
    ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧
      6 * D.card ≤ 2 * U.card + J.card + (J.filter (fun i => (edge i).card = 2)).card := by
  obtain ⟨D, hDU, hDhit, hDb⟩ := mixed_cover U J edge hsub
    (fun i hi => ⟨by have h := hrank i hi; omega, (hrank i hi).2⟩)
  have hpot : potential U J edge =
      2 * U.card + J.card + (J.filter (fun i => (edge i).card = 2)).card := by
    have hpoint : ∀ i ∈ J, edgeWeight (edge i).card =
        1 + if (edge i).card = 2 then 1 else 0 := by
      intro i hi
      have h := hrank i hi
      by_cases htwo : (edge i).card = 2
      · simp [htwo]
      · have hthree : (edge i).card = 3 := by omega
        simp [hthree]
    have hsum : (∑ i ∈ J, edgeWeight (edge i).card) =
        J.card + (J.filter (fun i => (edge i).card = 2)).card := by
      rw [sum_congr rfl hpoint, sum_add_distrib]
      simp only [sum_const, smul_eq_mul, mul_one]
      rw [← sum_filter]
      simp
    unfold potential
    rw [hsum]
    omega
  exact ⟨D, hDU, hDhit, by rwa [hpot] at hDb⟩

end TotalDominationAnnihilationProof.Hypergraph

#print axioms TotalDominationAnnihilationProof.Hypergraph.mixed_cover

