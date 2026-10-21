/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualFusionIntegral
import Proofs.RadenkovicGutmanIsoEnergy
import Proofs.RadenkovicGutmanCanonicalTreeCoverage

/-! Transfer exact finite spectral certificates to the actual core and arms.
The graph and the distinguished root are both transported. The target of a
finite certificate need not come with a separate treehood assumption: treehood
belongs to the actual source/fused pair and is already proved there.
-/
namespace Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
open CoreQuotient RootedTreeEnumeration CanonicalTreeCoverage
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem stopLoss_iso {G : SimpleGraph V} {H : SimpleGraph W}
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] (e : G ≃g H) (t : ℝ) :
    stopLoss (laplacianSpectrum G) t=stopLoss (laplacianSpectrum H) t := by
  have hg : dG=(fun a b => Classical.propDecidable (G.Adj a b)) := Subsingleton.elim _ _
  have hh : dH=(fun a b => Classical.propDecidable (H.Adj a b)) := Subsingleton.elim _ _
  rw [hg,hh]
  exact IsoEnergy.spectral_sum_eq e (fun x => max (x-t) 0)

def sourceIso {C : SimpleGraph V} {D : SimpleGraph W} (e : C ≃g D)
    (u : V) (p q : ℕ) : source C u p q ≃g source D (e u) p q where
  toEquiv := Equiv.sumCongr e.toEquiv (Equiv.refl _)
  map_rel_iff' := by
    intro a b
    have he : (⇑e.toEquiv : V → W)=(e : V → W) := rfl
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      simp only [source,joinTwo,SimpleGraph.sup_adj,SimpleGraph.sum,SimpleGraph.edge_adj,
        Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Equiv.refl_apply,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        he,e.map_adj_iff,e.injective.eq_iff,ne_eq,false_and,and_false,false_or,or_false,
        Bool.false_eq_true,not_false_eq_true,and_true]

def fusedIso {C : SimpleGraph V} {D : SimpleGraph W} (e : C ≃g D)
    (u : V) (p q : ℕ) : fused C u p q ≃g fused D (e u) p q where
  toEquiv := Equiv.sumCongr e.toEquiv (Equiv.refl _)
  map_rel_iff' := by
    intro a b
    have he : (⇑e.toEquiv : V → W)=(e : V → W) := rfl
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [fused,join,SimpleGraph.sup_adj,SimpleGraph.sum,SimpleGraph.edge_adj,
        Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Equiv.refl_apply,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        he,e.map_adj_iff,e.injective.eq_iff,ne_eq,false_and,and_false,false_or,or_false,
        Bool.false_eq_true,not_false_eq_true,and_true]

def acceptsGraphIso {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G : SimpleGraph A) (H : SimpleGraph B) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : A → B) : Bool :=
  decide (Function.Bijective f ∧ ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b)

def checkedGraphIso {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (G : SimpleGraph A) (H : SimpleGraph B) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : A → B) (h : acceptsGraphIso G H f=true) : G ≃g H where
  toEquiv := Equiv.ofBijective f (of_decide_eq_true h).1
  map_rel_iff' := (of_decide_eq_true h).2 _ _

theorem mean_positive_of_spectral_comparison (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1≤C.degree u)
    {N : ℕ} (G H : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (es : source C u p q ≃g G) (et : fused C u p q ≃g H)
    (hcomp : stopLoss (laplacianSpectrum H) (2-2/(N : ℝ))<
      stopLoss (laplacianSpectrum G) (2-2/(N : ℝ))) :
    0 < ActualFusionIntegral.normalizedIntegral C u p q
      (2-2/(Fintype.card (V ⊕ Fin (p+1) ⊕ Fin (q+1)) : ℝ)) := by
  classical
  rw [ActualFusionIntegral.integral_eq_delta C u p q hT hd]
  unfold ActualFusionIntegral.delta
  rw [stopLoss_iso es,stopLoss_iso et]
  have hc : Fintype.card (V ⊕ Fin (p+1) ⊕ Fin (q+1))=N := by
    simpa only [Fintype.card_fin] using Fintype.card_congr es.toEquiv
  rw [hc]
  exact sub_pos.mpr hcomp

def Certified (C : SimpleGraph V) (u : V) (p q : ℕ) : Prop :=
  ∃ (N : ℕ) (G H : SimpleGraph (Fin N)),
    Nonempty (source C u p q ≃g G) ∧ Nonempty (fused C u p q ≃g H) ∧
      stopLoss (laplacianSpectrum H) (2-2/(N : ℝ))<
        stopLoss (laplacianSpectrum G) (2-2/(N : ℝ))

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem certified_transport {C : SimpleGraph V} {D : SimpleGraph W} (e : C ≃g D)
    (u : V) (p q : ℕ) (h : Certified D (e u) p q) : Certified C u p q := by
  obtain ⟨N,G,H,⟨es⟩,⟨et⟩,hcomp⟩ := h
  exact ⟨N,G,H,⟨(sourceIso e u p q).trans es⟩,⟨(fusedIso e u p q).trans et⟩,hcomp⟩

theorem positive_of_certified (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1≤C.degree u) (h : Certified C u p q) :
    0 < ActualFusionIntegral.normalizedIntegral C u p q
      (2-2/(Fintype.card (V ⊕ Fin (p+1) ⊕ Fin (q+1)) : ℝ)) := by
  obtain ⟨N,G,H,⟨es⟩,⟨et⟩,hcomp⟩ := h
  exact mean_positive_of_spectral_comparison C u p q hT hd G H es et hcomp

#print axioms stopLoss_iso
#print axioms sourceIso
#print axioms fusedIso
#print axioms checkedGraphIso
#print axioms mean_positive_of_spectral_comparison
#print axioms certified_transport
#print axioms positive_of_certified
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
