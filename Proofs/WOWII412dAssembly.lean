import Proofs.WOWII412dCore
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Assembly reductions for WOWII 412d

The nonempty-core cover is an explicit hypothesis below. Its existence for every
bipartite graph is still to be proved. There is no global WOWII 412d theorem here.
-/
namespace WOWII412dCore
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma exists_bipartition (h : G.IsBipartite) : ∃ A : Finset V, Bipartition G A := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨univ.filter (fun v => c v = 0), ?_, ?_⟩
  · intro u hu v hv huv
    have hcu : c u = 0 := (mem_filter.mp hu).2
    have hcv : c v = 0 := (mem_filter.mp hv).2
    exact hc huv (hcu.trans hcv.symm)
  · intro u hu v hv huv
    have hcu : c u ≠ 0 := by simpa using (mem_sdiff.mp hu).2
    have hcv : c v ≠ 0 := by simpa using (mem_sdiff.mp hv).2
    have he : c u = c v := by omega
    exact hc huv he

lemma criticalUnion_eq_corona_of_bipartite (h : G.IsBipartite) :
    criticalUnion G = corona G := by
  obtain ⟨A, hA⟩ := exists_bipartition G h
  exact criticalUnion_eq_corona G A hA

/-- Once a core/excluded cover of the stated size exists, the global bound follows. -/
lemma total_bound_of_core_cover (h : G.IsBipartite) (D₀ : Finset V)
    (hD : ∀ v ∈ core G ∪ (univ \ corona G), ∃ w ∈ D₀, G.Adj v w)
    (hcard : D₀.card ≤ (core G).card) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  classical
  let R := corona G \ core G
  have htotal : G.IsTotalDominating ((D₀ ∪ R : Finset V) : Set V) := by
    intro v
    by_cases hv : v ∈ R
    · obtain ⟨w, hw, hvw⟩ := remainder_has_neighbor G v hv
      exact ⟨w, mem_union_right D₀ hw, hvw⟩
    · have hvc : v ∈ core G ∪ (univ \ corona G) := by
        simp only [R, mem_sdiff] at hv
        simp only [mem_union, mem_sdiff, mem_univ, true_and]
        tauto
      obtain ⟨w, hw, hvw⟩ := hD v hvc
      exact ⟨w, mem_union_left R hw, hvw⟩
  have hn : G.totalDominationNumber ≤ (D₀ ∪ R).card :=
    Nat.sInf_le ⟨D₀ ∪ R, htotal, rfl⟩
  have hc := card_sdiff_add_card_eq_card (core_subset_corona G)
  rw [criticalUnion_eq_corona_of_bipartite G h]
  have hu := card_union_le D₀ R
  dsimp [R] at hu hn
  omega

/-- The empty-core case of the theorem is fully proved. -/
lemma total_bound_of_core_empty (h : G.IsBipartite)
    (hni : ∀ v, ∃ w, G.Adj v w) (hempty : core G = ∅) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  classical
  obtain ⟨A, hA⟩ := exists_bipartition G h
  have hn := neighbors_core_eq G A hA
  have hne : neighbors G (core G) = ∅ := by simp [neighbors, hempty]
  have he : corona G = univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have : v ∈ neighbors G (core G) := by rw [hn]; simp [hv]
    simp [hne] at this
  rw [criticalUnion_eq_corona_of_bipartite G h, he]
  have ht : G.IsTotalDominating ((univ : Finset V) : Set V) := by
    intro v
    obtain ⟨w, hw⟩ := hni v
    exact ⟨w, mem_univ w, hw⟩
  exact Nat.sInf_le ⟨univ, ht, rfl⟩

#print axioms exists_bipartition
#print axioms total_bound_of_core_cover
#print axioms total_bound_of_core_empty
end WOWII412dCore
