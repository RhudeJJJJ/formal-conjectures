/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorAssembly
namespace Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorPredicate
open CoreQuotient ActualFusionIntegral OriginalAssembly DegreeOneMiddleAnchors
open scoped Classical
noncomputable section
def Proved (a : Anchor) : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u=1 →
      ((p=a.p ∧ q=a.q) ∨ (p=a.q ∧ q=a.p)) → order C p q≤a.n →
        (a.lower : ℝ)≤normalizedIntegral C u p q (2-2/(a.n : ℝ))
#print axioms Proved
end
end Gebendorfer.RadenkovicGutman.MiddleOriginalAnchorPredicate
