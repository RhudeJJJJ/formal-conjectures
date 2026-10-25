/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalDegree02ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree03ClassCertificates
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteAllCertificates
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeTwoThree
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=2 ∨ C.degree u=3) :
    0<meanIntegral C u p q :=
  DegreeTwoThreeDirectReserveAssembly.input_family
    OriginalDegree02ClassCertificates.certificates OriginalDegree03ClassCertificates.certificates
    DegreeTwoThreeFiniteAllCertificates.finite_cases m C u p q hT hd
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeTwoThree
