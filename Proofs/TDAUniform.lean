import Proofs.TDAHypergraphBase
import Proofs.ZajacBrooks

/-! The three-uniform Chvatal--McDiarmid bound with indexed repeated edges.
The bounded-incidence case uses the credited, rechecked Brooks theorem. -/

namespace TotalDominationAnnihilationProof.Hypergraph
open Finset SimpleGraph

variable {V I : Type*} [DecidableEq V]

private theorem three_cover_aux (edge : I → Finset V) (n : ℕ) :
    ∀ (U : Finset V) (J : Finset I), U.card + J.card ≤ n →
      (∀ i ∈ J, edge i ⊆ U) → (∀ i ∈ J, (edge i).card = 3) →
      ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧ 4 * D.card ≤ U.card + J.card := by
  classical
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro U J hn hsub hthree
    by_cases hhigh : ∃ v ∈ U, 3 ≤ (incident J edge v).card
    · obtain ⟨v, hv, hdegree⟩ := hhigh
      let K := J \ incident J edge v
      let U' := U.erase v
      have hincsub : incident J edge v ⊆ J := by
        intro i hi
        exact (mem_incident.mp hi).1
      have hKcard : K.card + (incident J edge v).card = J.card :=
        card_sdiff_add_card_eq_card hincsub
      have hUcard : U'.card + 1 = U.card := by
        dsimp [U']
        rw [card_erase_of_mem hv]
        have hpos := card_pos.mpr ⟨v, hv⟩
        omega
      have hstrict : U'.card + K.card < n := by omega
      have hsub' : ∀ i ∈ K, edge i ⊆ U' := by
        intro i hi w hw
        have hi' := mem_sdiff.mp hi
        apply mem_erase.mpr
        refine ⟨?_, hsub i hi'.1 hw⟩
        intro hwv
        exact hi'.2 (mem_incident.mpr ⟨hi'.1, hwv ▸ hw⟩)
      have hthree' : ∀ i ∈ K, (edge i).card = 3 := by
        intro i hi
        exact hthree i (mem_sdiff.mp hi).1
      obtain ⟨D, hDsub, hDhits, hDbound⟩ :=
        IH (U'.card + K.card) hstrict U' K le_rfl hsub' hthree'
      have hvD : v ∉ D := by
        intro hvD'
        exact (mem_erase.mp (hDsub hvD')).1 rfl
      refine ⟨insert v D, insert_subset hv (subset_trans hDsub (erase_subset _ _)), ?_, ?_⟩
      · intro i hi
        by_cases hvi : v ∈ edge i
        · exact ⟨v, mem_insert_self _ _, hvi⟩
        · have hiK : i ∈ K := mem_sdiff.mpr ⟨hi, by
            intro hmem
            exact hvi (mem_incident.mp hmem).2⟩
          obtain ⟨w, hwD, hwi⟩ := hDhits i hiK
          exact ⟨w, mem_insert_of_mem hwD, hwi⟩
      · rw [card_insert_of_notMem hvD]
        omega
    · have hdegree : ∀ v ∈ U, (incident J edge v).card ≤ 2 := by
        intro v hv
        by_contra hbad
        exact hhigh ⟨v, hv, by omega⟩
      have hcolor : (pairGraph U J edge).Colorable 4 := by
        apply Gebendorfer.Zajac.brooks_zajac 4 (by omega)
        · exact pairGraph_degree_le_four U J edge hthree
        · exact pairGraph_cliqueFree_five U J edge hthree
      exact three_cover_of_four_coloring U J edge hsub hthree hdegree hcolor

/-- Every indexed three-uniform finite hypergraph, including repeated edges,
has a transversal D with 4|D| at most its vertex count plus its edge count. -/
theorem three_uniform_cover (U : Finset V) (J : Finset I) (edge : I → Finset V)
    (hsub : ∀ i ∈ J, edge i ⊆ U) (hthree : ∀ i ∈ J, (edge i).card = 3) :
    ∃ D : Finset V, D ⊆ U ∧ Hits J edge D ∧ 4 * D.card ≤ U.card + J.card :=
  three_cover_aux edge (U.card + J.card) U J le_rfl hsub hthree

end TotalDominationAnnihilationProof.Hypergraph

#print axioms TotalDominationAnnihilationProof.Hypergraph.three_uniform_cover
