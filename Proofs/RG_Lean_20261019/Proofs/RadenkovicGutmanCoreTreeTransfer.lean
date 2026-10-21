/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeTransfer
namespace Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
open CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- The actual residual core is a tree whenever its two-arm source is a tree. -/
theorem core_tree {V : Type} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    (u : V) (p q : ℕ) (hT : (source C u p q).IsTree) : C.IsTree := by
  classical
  let color : (V ⊕ Fin (p+1) ⊕ Fin (q+1)) → C.ConnectedComponent :=
    fun x => match x with
      | .inl v => C.connectedComponentMk v
      | .inr _ => C.connectedComponentMk u
  have hc : ∀ a b, (source C u p q).Adj a b → color a=color b := by
    intro a b h
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    all_goals first
      | rfl
      | (apply SimpleGraph.ConnectedComponent.sound
         apply SimpleGraph.Adj.reachable
         simpa only [source,joinTwo,SimpleGraph.sup_adj,SimpleGraph.sum,
           SimpleGraph.edge_adj,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
           false_and,and_false,false_or,or_false,Bool.false_eq_true] using h)
      | (simp_all [color,source,joinTwo,SimpleGraph.sum,SimpleGraph.edge_adj])
  have hw : ∀ {a b} (walk : (source C u p q).Walk a b), color a=color b := by
    intro a b walk
    induction walk with
    | nil => rfl
    | @cons a b c hab walk ih => exact (hc a b hab).trans ih
  have connected : C.Connected := by
    let : Nonempty V := ⟨u⟩
    constructor
    intro v w
    obtain ⟨walk⟩ := hT.connected (.inl v) (.inl w)
    exact SimpleGraph.ConnectedComponent.exact (hw walk)
  let f : C →g source C u p q := ⟨Sum.inl,by
    intro a b h
    simpa [source,joinTwo,SimpleGraph.sum,SimpleGraph.edge_adj] using h⟩
  exact ⟨connected,hT.isAcyclic.comap f Sum.inl_injective⟩

#print axioms core_tree
end
end Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
