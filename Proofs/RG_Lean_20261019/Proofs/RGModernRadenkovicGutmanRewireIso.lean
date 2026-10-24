module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The explicit all-length isomorphism between the fused joined-path graph and
the delete/add rewiring on the original labelled vertex set.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Definition 1.2.
-/
public import Proofs.RGModernRadenkovicGutmanFusionQuotient
public import Proofs.RGModernRadenkovicGutmanCountTransport

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.RewireIso

open scoped Classical
noncomputable section

variable {V : Type*}

def base (C : SimpleGraph V) (u : V) (p q : ℕ) :
    SimpleGraph (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :=
  (C ⊕g (SimpleGraph.pathGraph (p + 1) ⊕g SimpleGraph.pathGraph (q + 1))) ⊔
    SimpleGraph.edge (.inl u) (.inr (.inl 0))

def rewired (C : SimpleGraph V) (u : V) (p q : ℕ) :
    SimpleGraph (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :=
  base C u p q ⊔ SimpleGraph.edge (.inr (.inl (Fin.last p))) (.inr (.inr 0))

def armEquiv (p q : ℕ) : Fin (p + 1) ⊕ Fin (q + 1) ≃ Fin (p + q + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

def vertices (p q : ℕ) : (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) ≃ (V ⊕ Fin (p + q + 2)) :=
  Equiv.sumCongr (Equiv.refl V) (armEquiv p q)

theorem armEquiv_left (p q : ℕ) (i : Fin (p + 1)) :
    (armEquiv p q (.inl i)).val = i.val := by
  simp [armEquiv]

theorem armEquiv_right (p q : ℕ) (i : Fin (q + 1)) :
    (armEquiv p q (.inr i)).val = p + 1 + i.val := by
  simp [armEquiv]

theorem rewired_adj (C : SimpleGraph V) (u : V) (p q : ℕ)
    (i j : V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :
    (rewired C u p q).Adj i j ↔
      (CoreQuotient.fused C u p q).Adj (vertices p q i) (vertices p q j) := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [rewired, base, CoreQuotient.fused, CoreQuotient.join,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj, SimpleGraph.sum,
      vertices, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
      Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false, false_or, or_false,
      SimpleGraph.pathGraph_adj]
  all_goals simp only [Fin.ext_iff, armEquiv_left, armEquiv_right, Fin.val_zero,
    Fin.val_last, ne_eq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
    Bool.false_eq_true, false_or, and_true,
    not_false_eq_true]
  all_goals first | rfl | omega | (constructor <;> intro h <;> simp_all)

/-- All positive arm lengths, including singleton arms, on the original vertex set. -/
def fusedIso (C : SimpleGraph V) (u : V) (p q : ℕ) :
    rewired C u p q ≃g CoreQuotient.fused C u p q where
  toEquiv := vertices p q
  map_rel_iff' := fun {i j} => (rewired_adj C u p q i j).symm

theorem source_eq (C : SimpleGraph V) (u : V) (p q : ℕ) :
    CoreQuotient.source C u p q =
      base C u p q ⊔ SimpleGraph.edge (.inl u) (.inr (.inr 0)) := rfl

theorem base_missing_edges (C : SimpleGraph V) (u : V) (p q : ℕ) :
    ¬(base C u p q).Adj (.inl u) (.inr (.inr 0)) ∧
      ¬(base C u p q).Adj (.inr (.inl (Fin.last p))) (.inr (.inr 0)) := by
  simp [base, SimpleGraph.sum, SimpleGraph.edge_adj]

#print axioms fusedIso
#print axioms base_missing_edges

end
end Gebendorfer.RadenkovicGutman.RewireIso
