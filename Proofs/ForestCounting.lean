import FormalConjecturesUtil

/-! Finite forest counts, retaining all isolated components. -/
namespace ForestCounting
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma component_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) [Fintype c] [DecidableRel c.toSimpleGraph.Adj]
    (v : c) : c.toSimpleGraph.degree v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact {
    toFun := fun w => ⟨w.val.val, w.property⟩
    invFun := fun w => ⟨⟨w.val, (c.mem_supp_congr_adj w.property).mp v.property⟩,w.property⟩
    left_inv := by intro w; rfl
    right_inv := by intro w; rfl }

lemma forest_card (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card + Nat.card G.ConnectedComponent = Fintype.card V := by
  classical
  let C := G.ConnectedComponent
  let : (c : C) → Fintype c := fun _ => Fintype.ofFinite _
  let : (c : C) → DecidableRel c.toSimpleGraph.Adj := fun _ => Classical.decRel _
  have hc (c : C) :
      (∑ v : c, G.degree v) + 2 = 2 * Fintype.card c := by
    have ht := (hG.isTree_connectedComponent c).card_edgeFinset
    have hs := c.toSimpleGraph.sum_degrees_eq_twice_card_edges
    simp_rw [component_degree G c] at hs
    omega
  let hequiv : (Σ c : C, c) ≃ V := {
    toFun := fun p => p.2.val
    invFun := fun v => ⟨G.connectedComponentMk v, ⟨v,rfl⟩⟩
    left_inv := by
      rintro ⟨c,v,hv⟩
      have h : G.connectedComponentMk v = c := hv
      subst c; rfl
    right_inv := by intro v; rfl }
  have hn : (∑ c : C, Fintype.card c) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr hequiv
  have hd : (∑ c : C, ∑ v : c, G.degree v) = ∑ v : V, G.degree v := by
    calc
      _ = ∑ p : (Σ c : C, c), G.degree p.2.val :=
        (Fintype.sum_sigma (fun p : (Σ c : C, c) => G.degree p.2.val)).symm
      _ = _ := Fintype.sum_equiv hequiv _ _ (fun _ => rfl)
  have hh := congrArg (fun f : C → ℕ => ∑ c, f c) (funext hc)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum] at hh
  rw [hd, hn, G.sum_degrees_eq_twice_card_edges] at hh
  rw [Nat.card_eq_fintype_card]
  change 2 * G.edgeFinset.card + Fintype.card G.ConnectedComponent * 2 =
    2 * Fintype.card V at hh
  omega

def innerEdges (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ A

@[simp] lemma mem_innerEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (u v : V) :
    s(u,v) ∈ innerEdges G A ↔ G.Adj u v ∧ u ∈ A ∧ v ∈ A := by
  simp [innerEdges, Sym2.toFinset_mk_eq, insert_subset_iff]

noncomputable def components (G : SimpleGraph V) (A : Finset V) : ℕ :=
  Nat.card (G.induce (A : Set V)).ConnectedComponent

lemma forest_on (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (A : Finset V) :
    (innerEdges G A).card + components G A = A.card := by
  classical
  rw [innerEdges, G.card_filter_edgeFinset_toFinset_subset]
  have hf := forest_card (G.induce (A : Set V))
    (hG.induce (A : Set V))
  change (G.induce (A : Set V)).edgeFinset.card + components G A = A.card
  have hc : Fintype.card (A : Set V) = A.card := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hc] at hf
  exact hf

/-- Each component of a selected subset can be charged to a distinct edge
of an ambient totally dominated induced subgraph. -/
lemma components_le_innerEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (D I : Finset V) (hID : I ⊆ D)
    (hD : ∀ v ∈ D, ∃ w ∈ D, G.Adj v w) :
    components G I ≤ (innerEdges G D).card := by
  classical
  let H := G.induce (I : Set V)
  choose v hv using (fun c : H.ConnectedComponent => c.nonempty_supp)
  choose w hwD hadj using (fun c : H.ConnectedComponent => hD (v c).val (hID (v c).property))
  let f : H.ConnectedComponent → {e // e ∈ innerEdges G D} := fun c =>
    ⟨s((v c).val,w c), (mem_innerEdges G D _ _).mpr
      ⟨hadj c,hID (v c).property,hwD c⟩⟩
  have hfinj : Function.Injective f := by
    intro c d heq
    have he := congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp he with he | he
    · have hverts : v c = v d := Subtype.ext he.1
      exact (hv c).symm.trans (hverts ▸ hv d)
    · have hreach : H.Reachable (v c) (v d) :=
        (show H.Adj (v c) (v d) from by change G.Adj (v c).val (v d).val; rw [← he.2]; exact hadj c).reachable
      exact (hv c).symm.trans ((ConnectedComponent.sound hreach).trans (hv d))
  have hh := Nat.card_le_card_of_injective f hfinj
  simpa only [components, H, Nat.card_eq_fintype_card, Fintype.card_coe] using hh

end ForestCounting
