/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII271Proof

namespace WOWII271Audit
open SimpleGraph

/-- Exact proposed repository type, independently restated without importing a placeholder. -/
theorem exact_statement {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    let dM := (M ×ˢ M).sup fun p => G.dist p.1 p.2
    ⌈Real.sqrt (2 * dM : ℝ)⌉₊ ≤ G.totalDominationNumber := by
  exact WOWII271Proof.conjecture271 G hG

/-- The maximum is over a genuinely nonempty set of pairs, not an empty-supremum default. -/
theorem maximum_degree_pairs_nonempty {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    (M ×ˢ M).Nonempty := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  exact ⟨(v,v), Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.symm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.symm⟩⟩⟩

#print axioms WOWII271Proof.component_distance_bound
#print axioms WOWII271Proof.total_domination_distance_bound
#print axioms WOWII271Proof.maximum_degree_distance_of_pair
#print axioms WOWII271Proof.squared_bound_for_set
#print axioms WOWII271Proof.conjecture271
#print axioms exact_statement
#print axioms maximum_degree_pairs_nonempty

end WOWII271Audit
