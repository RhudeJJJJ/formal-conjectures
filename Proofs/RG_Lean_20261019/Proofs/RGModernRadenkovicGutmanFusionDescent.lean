module
/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
public import Proofs.RGModernRadenkovicGutmanRewireTopology
public import Proofs.RGModernRadenkovicGutmanRewireIso

@[expose] public section

/-!
# Leaf descent for the actual RG source and fused graphs

The indices `p` and `q` are physical arm lengths minus one. In particular,
`p = 0` and `q = 0` are included. The residual degree is the degree in `C`.
-/

namespace Gebendorfer.RadenkovicGutman.FusionDescent

open SimpleGraph CoreQuotient RewireIso RewireTopology
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V]

theorem base_root_degree (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (base C u p q).degree (.inl u) = C.degree u + 1 := by
  calc
    _ = ∑ j, if (base C u p q).Adj (.inl u) j
        then 1 else 0 := by
      simpa only [Nat.cast_id] using
        (base C u p q).degree_eq_sum_if_adj (R := ℕ) (.inl u)
    _ = (∑ j, if C.Adj u j then 1 else 0) + 1 := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp [base, SimpleGraph.sum, edge_adj]
    _ = _ := by
      congr 1
      simpa only [Nat.cast_id] using (C.degree_eq_sum_if_adj (R := ℕ) u).symm

theorem base_endpoint_degree (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (base C u p q).degree (.inr (.inl (Fin.last p))) = 1 := by
  cases p with
  | zero =>
    have hn : (base C u 0 q).neighborFinset (.inr (.inl (Fin.last 0))) = {.inl u} := by
      ext (x | (x | x)) <;>
        simp [base, SimpleGraph.sum, edge_adj, pathGraph_adj, Fin.ext_iff]
    rw [degree, hn, Finset.card_singleton]
  | succ p =>
    have hn : (base C u (p + 1) q).neighborFinset (.inr (.inl (Fin.last (p + 1)))) =
        {.inr (.inl (⟨p, by omega⟩ : Fin (p + 1 + 1)))} := by
      ext (x | (x | x)) <;>
        simp only [mem_neighborFinset, base, sup_adj, SimpleGraph.sum, edge_adj,
          pathGraph_adj, Finset.mem_singleton, Sum.inr.injEq, Sum.inl.injEq,
          Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false, false_or, or_false,
          Fin.ext_iff, Fin.val_last, Fin.val_zero, Bool.false_eq_true]
      · constructor
        · rintro ⟨⟨h, _⟩, _⟩
          omega
        · intro h
          exact h.elim
      · omega
    rw [degree, hn, Finset.card_singleton]

omit [Fintype V] in
theorem base_root_endpoint_reachable (C : SimpleGraph V) (u : V) (p q : ℕ) :
    (base C u p q).Reachable (.inl u) (.inr (.inl (Fin.last p))) := by
  let f : pathGraph (p + 1) →g base C u p q :=
    { toFun := fun i => .inr (.inl i)
      map_rel' := by intro a b hab; exact Or.inl hab }
  have hpath := (pathGraph_preconnected (p + 1) 0 (Fin.last p)).map f
  have hedge : (base C u p q).Adj (.inl u) (.inr (.inl 0)) := by
    exact Or.inr (by simp [edge_adj])
  exact hedge.reachable.trans hpath

/-- The original and fused trees have the same order and differ by exactly one leaf.
Only treehood of the actual input and positive residual degree are required. -/
theorem fusion_tree_and_leaf_count (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    (fused C u p q).IsTree ∧
      Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) =
        Fintype.card (V ⊕ Fin (p + q + 2)) ∧
      leafCount (source C u p q) = leafCount (fused C u p q) + 1 := by
  have hmissing := base_missing_edges C u p q
  have hr := base_root_endpoint_reachable C u p q
  have ht := tree_rewire (base C u p q) (.inl u) (.inr (.inl (Fin.last p)))
    (.inr (.inr 0)) (by simp) (by simp) hmissing.1 hmissing.2 hr hT
  have hl := leaf_count_rewire (base C u p q) (.inl u) (.inr (.inl (Fin.last p)))
    (.inr (.inr 0)) (by simp) (by simp) (by simp) hmissing.1 hmissing.2
    (by rw [base_root_degree]; omega) (base_endpoint_degree C u p q)
  change (rewired C u p q).IsTree at ht
  have hleaf := leaf_count_iso (fusedIso C u p q)
  refine ⟨(fusedIso C u p q).isTree_iff.mp ht, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · change leafCount (source C u p q) = leafCount (rewired C u p q) + 1 at hl
    exact hl.trans (congrArg (· + 1) hleaf)

theorem fusion_leaf_count_strict (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    leafCount (fused C u p q) < leafCount (source C u p q) := by
  rw [(fusion_tree_and_leaf_count C u p q hT hd).2.2]
  omega

#print axioms base_root_degree
#print axioms base_endpoint_degree
#print axioms base_root_endpoint_reachable
#print axioms fusion_tree_and_leaf_count
#print axioms fusion_leaf_count_strict

end
end Gebendorfer.RadenkovicGutman.FusionDescent
