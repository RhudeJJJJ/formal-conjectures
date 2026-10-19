import Proofs.TDAMixed
import Proofs.TDABudget

/-! Truncation retains actual neighborhood vertices and the original row indices. -/

namespace TotalDominationAnnihilationProof.Hypergraph
open Finset

variable {V I : Type*} [DecidableEq V]

noncomputable def trimThree (A : Finset V) : Finset V :=
  if h : 3 ≤ A.card then Classical.choose (exists_subset_card_eq h) else A

omit [DecidableEq V] in
theorem trimThree_subset (A : Finset V) : trimThree A ⊆ A := by
  unfold trimThree
  split_ifs with h
  · exact (Classical.choose_spec (exists_subset_card_eq h)).1
  · exact subset_refl _

omit [DecidableEq V] in
theorem trimThree_card (A : Finset V) : (trimThree A).card = min 3 A.card := by
  unfold trimThree
  split_ifs with h
  · rw [(Classical.choose_spec (exists_subset_card_eq h)).2, min_eq_left h]
  · rw [min_eq_right (by omega)]

open scoped Classical in
/-- General neighborhood cover: large rows are replaced by actual three-element subsets. -/
theorem neighborhood_cover (Q : Finset V) (J : Finset I) (N : I → Finset V)
    (hsub : ∀ i ∈ J, N i ⊆ Q) (hsize : ∀ i ∈ J, 2 ≤ (N i).card) :
    ∃ D : Finset V, D ⊆ Q ∧ Hits J N D ∧
      6 * D.card ≤ 2 * Q.card + J.card + (J.filter (fun i => (N i).card = 2)).card := by
  let edge := fun i => trimThree (N i)
  have hsub' : ∀ i ∈ J, edge i ⊆ Q := fun i hi =>
    subset_trans (trimThree_subset _) (hsub i hi)
  have hsize' : ∀ i ∈ J, 2 ≤ (edge i).card ∧ (edge i).card ≤ 3 := by
    intro i hi
    dsimp [edge]
    rw [trimThree_card]
    have h := hsize i hi
    omega
  obtain ⟨D, hDQ, hDhit, hDb⟩ := mixed_cover_two_three Q J edge hsub' hsize'
  have hfilter : J.filter (fun i => (edge i).card = 2) =
      J.filter (fun i => (N i).card = 2) := by
    ext i
    simp only [mem_filter, edge, trimThree_card]
    constructor
    · rintro ⟨hi, hc⟩
      exact ⟨hi, by omega⟩
    · rintro ⟨hi, hc⟩
      exact ⟨hi, by omega⟩
  refine ⟨D, hDQ, ?_, ?_⟩
  · intro i hi
    obtain ⟨v, hvD, hve⟩ := hDhit i hi
    exact ⟨v, hvD, trimThree_subset (N i) hve⟩
  · rwa [hfilter] at hDb

end TotalDominationAnnihilationProof.Hypergraph

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The leaf-free covering bridge uses the full indexed open-neighborhood family. -/
theorem total_domination_bound_min_degree_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ v, 2 ≤ G.degree v) :
    6 * G.totalDominationNumber ≤ 3 * Fintype.card V +
      (univ.filter (fun v => G.degree v = 2)).card := by
  classical
  obtain ⟨D, _, hDhit, hDb⟩ := Hypergraph.neighborhood_cover univ univ
    (fun v => G.neighborFinset v) (by intro i _; exact subset_univ _)
    (by intro v _; exact hdegree v)
  have hTD : G.IsTotalDominating (D : Set V) := by
    intro v
    obtain ⟨w, hwD, hwN⟩ := hDhit v (mem_univ v)
    exact ⟨w, hwD, (SimpleGraph.mem_neighborFinset _ _ _).mp hwN⟩
  have hle := totalDominationNumber_le_card G D hTD
  change 6 * D.card ≤ 2 * Fintype.card V + Fintype.card V +
    (univ.filter (fun v => G.degree v = 2)).card at hDb
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.total_domination_bound_min_degree_two
