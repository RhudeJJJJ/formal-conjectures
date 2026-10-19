import Proofs.TDAGraphBasics

/-! Exact counts for the leaf/core decomposition. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def leafNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (leaves G).filter fun p => G.Adj v p

theorem degree_core_add_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (coreNeighbors G v).card + (leafNeighbors G v).card = G.degree v := by
  classical
  have hdis : Disjoint (coreNeighbors G v) (leafNeighbors G v) := by
    apply Finset.disjoint_left.mpr
    intro p hpK hpL
    exact (mem_sdiff.mp hpK).2 (mem_filter.mp hpL).1
  have hunion : coreNeighbors G v ∪ leafNeighbors G v = G.neighborFinset v := by
    ext p
    simp only [coreNeighbors, leafNeighbors, mem_union, mem_sdiff, mem_filter, mem_neighborFinset]
    tauto
  rw [← card_union_of_disjoint hdis, hunion]
  rfl

theorem sum_leaf_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) :
    (∑ v ∈ core G, (leafNeighbors G v).card) = (leaves G).card := by
  classical
  simp only [leafNeighbors, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hpoint : ∀ p ∈ leaves G,
      (∑ v ∈ core G, if G.Adj v p then (1 : ℕ) else 0) = 1 := by
    intro p hp
    rw [← sum_filter]
    have heq : (core G).filter (fun v => G.Adj v p) = G.neighborFinset p := by
      ext v
      simp only [mem_filter, mem_neighborFinset]
      constructor
      · exact fun h => h.2.symm
      · intro hpv
        refine ⟨mem_core.mpr ?_, hpv.symm⟩
        intro hv
        exact leaves_not_adjacent G hG hn hp (mem_leaves.mpr hv) hpv
    rw [heq, sum_const]
    simpa using mem_leaves.mp hp
  rw [sum_congr rfl hpoint]

theorem supports_card_le_leaves (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) :
    (supports G).card ≤ (leaves G).card := by
  classical
  have hpoint : ∀ v ∈ supports G, 1 ≤ (leafNeighbors G v).card := by
    intro v hv
    obtain ⟨p, hp, hvp⟩ := mem_supports.mp hv
    exact card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, hvp⟩⟩
  calc
    _ = ∑ _v ∈ supports G, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ supports G, (leafNeighbors G v).card := sum_le_sum hpoint
    _ ≤ ∑ v ∈ core G, (leafNeighbors G v).card :=
      sum_le_sum_of_subset_of_nonneg (supports_subset_core G hG hn) (by intros; omega)
    _ = _ := sum_leaf_neighbors G hG hn

/-- Each core vertex of degree one spends either a global degree-two vertex or
an additional leaf; this bounds all such corrections in one sum. -/
theorem core_small_degree_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (hn : 3 ≤ Fintype.card V) :
    2 * ((core G).filter (fun v => (coreNeighbors G v).card = 1)).card +
      ((core G).filter (fun v => (coreNeighbors G v).card = 2)).card ≤
      (univ.filter (fun v => G.degree v = 2)).card + (leaves G).card := by
  classical
  have hpoint : ∀ v ∈ core G,
      2 * (if (coreNeighbors G v).card = 1 then 1 else 0) +
        (if (coreNeighbors G v).card = 2 then 1 else 0) ≤
        (if G.degree v = 2 then 1 else 0) + (leafNeighbors G v).card := by
    intro v hv
    have hdeg := degree_core_add_leaf G v
    have hne := mem_core.mp hv
    split_ifs <;> omega
  have hs := sum_le_sum hpoint
  have hleaf := sum_leaf_neighbors G hG hn
  have hglobal : ((core G).filter (fun v => G.degree v = 2)).card ≤
      (univ.filter (fun v => G.degree v = 2)).card :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [← sum_filter, ← sum_filter, ← sum_filter] at hs
  simp only [sum_const, smul_eq_mul, mul_one] at hs
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.sum_leaf_neighbors
#print axioms TotalDominationAnnihilationProof.core_small_degree_count
