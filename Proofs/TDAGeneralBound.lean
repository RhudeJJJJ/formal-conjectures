import Proofs.TDACoreCover
import Proofs.TDALeafCounts

/-! The general covering bound, including adjacent and strong supports. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The leaf/core proof pays the degree-one core correction directly from leaf
multiplicities; no restriction on supports is imposed. -/
theorem total_domination_general_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : 3 ≤ Fintype.card V) :
    6 * G.totalDominationNumber ≤ 3 * Fintype.card V + 2 * (leaves G).card +
      (univ.filter (fun v => G.degree v = 2)).card := by
  classical
  have hKL : (core G).card + (leaves G).card = Fintype.card V := by
    have h := card_sdiff_add_card_eq_card (subset_univ (leaves G))
    simpa only [core, card_univ] using h
  by_cases hcore : 2 ≤ (core G).card
  · have hNS : ∀ v ∈ core G, coreNeighbors G v ⊆ core G := by
      intro v _ w hw
      exact (mem_coreNeighbors.mp hw).2
    let N := fun v => if v ∈ core G then coreNeighbors G v else ∅
    have hNcore : ∀ v ∈ core G, N v = coreNeighbors G v := by
      intro v hv
      simp only [N, if_pos hv]
    have hNsym : ∀ u v, v ∈ N u ↔ u ∈ N v := by
      intro u v
      by_cases hu : u ∈ core G <;> by_cases hv : v ∈ core G
      · simp only [N, if_pos hu, if_pos hv, mem_coreNeighbors, hu, hv, and_true]
        exact G.adj_comm u v
      · simp only [N, if_pos hu, if_neg hv, mem_coreNeighbors, hv, and_false, notMem_empty]
      · simp only [N, if_neg hu, if_pos hv, mem_coreNeighbors, hu, and_false, notMem_empty]
      · simp only [N, if_neg hu, if_neg hv, notMem_empty]
    have hNsub : ∀ v ∈ core G, N v ⊆ core G := by
      intro v hv
      rw [hNcore v hv]
      exact hNS v hv
    have hNnon : ∀ v ∈ core G, (N v).Nonempty := by
      intro v hv
      rw [hNcore v hv]
      exact core_neighbor_nonempty G hG.preconnected hcore hv
    have hone : ∀ v ∈ core G, (N v).card = 1 → v ∈ supports G := by
      intro v hv h1
      rw [hNcore v hv] at h1
      have hdeg := degree_core_add_leaf G v
      have hne := mem_core.mp hv
      have hp : 0 < (leafNeighbors G v).card := by omega
      obtain ⟨p, hp⟩ := card_pos.mp hp
      exact mem_supports.mpr ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    obtain ⟨D, _, hSD, hDcore, hDb⟩ := core_cover (core G) (supports G) N hNsub hNsym
      hNnon (supports_subset_core G hG.preconnected hn) hone
    have hTD : G.IsTotalDominating (D : Set V) := by
      intro v
      by_cases hv : v ∈ core G
      · obtain ⟨w, hwD, hwN⟩ := hDcore v hv
        rw [hNcore v hv] at hwN
        exact ⟨w, hwD, (mem_coreNeighbors.mp hwN).1⟩
      · have hvL : v ∈ leaves G := by simpa using hv
        have hp := mem_leaves.mp hvL
        obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj _).mp (by omega : 0 < G.degree v)
        have hwS : w ∈ supports G := mem_supports.mpr ⟨v, hvL, hvw.symm⟩
        exact ⟨w, hSD hwS, hvw⟩
    have hfilters : ∀ k : ℕ, (core G).filter (fun v => (N v).card = k) =
        (core G).filter (fun v => (coreNeighbors G v).card = k) := by
      intro k
      apply filter_congr
      intro v hv
      rw [hNcore v hv]
    rw [hfilters 1, hfilters 2] at hDb
    have hc := core_small_degree_count G hG.preconnected hn
    have hs := supports_card_le_leaves G hG.preconnected hn
    have hle := totalDominationNumber_le_card G D hTD
    omega
  · have hne := core_nonempty G hG hn
    have hc1 : (core G).card = 1 := by have hp := card_pos.mpr hne; omega
    obtain ⟨c, hc⟩ := card_eq_one.mp hc1
    let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨w, hcw⟩ := (G.degree_pos_iff_exists_adj _).mp (hG.preconnected.degree_pos_of_nontrivial c)
    have hvc : ∀ v, v ≠ c → G.Adj v c := by
      intro v hvc
      have hvL : v ∈ leaves G := by
        by_contra hbad
        have hvK : v ∈ core G := mem_core.mpr (by simpa using hbad)
        rw [hc] at hvK
        exact hvc (mem_singleton.mp hvK)
      obtain ⟨q, hvq⟩ := (G.degree_pos_iff_exists_adj _).mp (by rw [mem_leaves.mp hvL]; omega)
      have hqK : q ∈ core G := by
        apply mem_core.mpr
        intro hqL
        exact leaves_not_adjacent G hG.preconnected hn hvL (mem_leaves.mpr hqL) hvq
      rw [hc] at hqK
      rwa [mem_singleton.mp hqK] at hvq
    have hTD : G.IsTotalDominating (({c, w} : Finset V) : Set V) := by
      intro v
      by_cases hvc' : v = c
      · subst v
        exact ⟨w, by simp, hcw⟩
      · exact ⟨c, by simp, hvc v hvc'⟩
    have hle := totalDominationNumber_le_card G {c, w} hTD
    have hp : ({c, w} : Finset V).card ≤ 2 := by simpa using (card_insert_le c ({w} : Finset V))
    omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.total_domination_general_bound
