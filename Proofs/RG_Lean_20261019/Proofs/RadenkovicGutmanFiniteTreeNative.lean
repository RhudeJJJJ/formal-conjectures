/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeTransfer
namespace Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
open CoreQuotient RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0

def sourceLabel (n p q : ℕ) :
    (Vertices n ⊕ Fin (p+1) ⊕ Fin (q+1)) → Fin (n+p+q+3)
  | .inl v => ⟨(label v).val,by have := (label v).isLt; omega⟩
  | .inr (.inl i) => ⟨n+1+i.val,by have := i.isLt; omega⟩
  | .inr (.inr j) => ⟨n+p+2+j.val,by have := j.isLt; omega⟩

def fusedLabel (n p q : ℕ) : (Vertices n ⊕ Fin (p+q+2)) → Fin (n+p+q+3)
  | .inl v => ⟨(label v).val,by have := (label v).isLt; omega⟩
  | .inr i => ⟨n+1+i.val,by have := i.isLt; omega⟩

instance sourceDecidable {n : ℕ} (t : Family n) (p q : ℕ) :
    DecidableRel (source (graph t) (root n) p q).Adj := by
  unfold source joinTwo
  infer_instance

instance fusedDecidable {n : ℕ} (t : Family n) (p q : ℕ) :
    DecidableRel (fused (graph t) (root n) p q).Adj := by
  unfold fused join
  infer_instance

noncomputable section

theorem of_native_maps {n p q N : ℕ} (t : Family n)
    (G H : SimpleGraph (Fin N)) [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj]
    (f : (Vertices n ⊕ Fin (p+1) ⊕ Fin (q+1)) → Fin N)
    (g : (Vertices n ⊕ Fin (p+q+2)) → Fin N)
    (hf : acceptsGraphIso (source (graph t) (root n) p q) G f=true)
    (hg : acceptsGraphIso (fused (graph t) (root n) p q) H g=true)
    (hcomp : stopLoss (laplacianSpectrum H) (2-2/(N : ℝ))<
      stopLoss (laplacianSpectrum G) (2-2/(N : ℝ))) :
    Certified (graph t) (root n) p q := by
  refine ⟨N,G,H,⟨checkedGraphIso _ _ f hf⟩,⟨checkedGraphIso _ _ g hg⟩,?_⟩
  have hG : dG=(fun i j => Classical.propDecidable (G.Adj i j)) := Subsingleton.elim _ _
  have hH : dH=(fun i j => Classical.propDecidable (H.Adj i j)) := Subsingleton.elim _ _
  rw [← hG,← hH]
  exact hcomp

#print axioms of_native_maps
end
end Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
