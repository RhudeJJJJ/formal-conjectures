/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeTransfer
namespace Gebendorfer.RadenkovicGutman.FiniteTreeTransfer
open CoreQuotient RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0

instance nativeSumDecidable {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl a, .inl b => dG a b
  | .inr a, .inr b => dH a b
  | .inl _, .inr _ => inferInstanceAs (Decidable (false=true))
  | .inr _, .inl _ => inferInstanceAs (Decidable (false=true))

instance (priority := 2000) nativeEdgeDecidable {A : Type} [DecidableEq A] (a b : A) :
    DecidableRel (SimpleGraph.edge a b).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet {s(a,b)}).Adj)

instance (priority := 2000) nativePathDecidable (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := fun a b => by
  change Decidable (a ⋖ b ∨ b ⋖ a)
  unfold CovBy
  infer_instance

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
  let A := Vertices n ⊕ Fin (p+1) ⊕ Fin (q+1)
  let forest : SimpleGraph A := graph t ⊕g
    (SimpleGraph.pathGraph (p+1) ⊕g SimpleGraph.pathGraph (q+1))
  let edgeOne : SimpleGraph A := SimpleGraph.edge (.inl (root n)) (.inr (.inl 0))
  let edgeTwo : SimpleGraph A := SimpleGraph.edge (.inl (root n)) (.inr (.inr 0))
  let dForest : DecidableRel forest.Adj :=
    @nativeSumDecidable (Vertices n) (Fin (p+1) ⊕ Fin (q+1)) (graph t)
      (SimpleGraph.pathGraph (p+1) ⊕g SimpleGraph.pathGraph (q+1))
      (CanonicalTreeCoverage.graphDecidable t)
      (@nativeSumDecidable (Fin (p+1)) (Fin (q+1))
        (SimpleGraph.pathGraph (p+1)) (SimpleGraph.pathGraph (q+1))
        (nativePathDecidable (p+1)) (nativePathDecidable (q+1)))
  let dOne : DecidableRel edgeOne.Adj := nativeEdgeDecidable _ _
  let dTwo : DecidableRel edgeTwo.Adj := nativeEdgeDecidable _ _
  exact fun a b => @instDecidableOr (forest.Adj a b ∨ edgeOne.Adj a b) (edgeTwo.Adj a b)
    (@instDecidableOr (forest.Adj a b) (edgeOne.Adj a b) (dForest a b) (dOne a b)) (dTwo a b)

instance fusedDecidable {n : ℕ} (t : Family n) (p q : ℕ) :
    DecidableRel (fused (graph t) (root n) p q).Adj := by
  let A := Vertices n ⊕ Fin (p+q+2)
  let forest : SimpleGraph A := graph t ⊕g SimpleGraph.pathGraph (p+q+2)
  let edgeOne : SimpleGraph A := SimpleGraph.edge (.inl (root n)) (.inr 0)
  let dForest : DecidableRel forest.Adj :=
    @nativeSumDecidable (Vertices n) (Fin (p+q+2)) (graph t)
      (SimpleGraph.pathGraph (p+q+2)) (CanonicalTreeCoverage.graphDecidable t)
      (nativePathDecidable (p+q+2))
  let dOne : DecidableRel edgeOne.Adj := nativeEdgeDecidable _ _
  exact fun a b => @instDecidableOr (forest.Adj a b) (edgeOne.Adj a b) (dForest a b) (dOne a b)

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
