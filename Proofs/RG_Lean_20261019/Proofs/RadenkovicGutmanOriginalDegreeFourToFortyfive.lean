/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Mathlib.Tactic.IntervalCases
import Proofs.RadenkovicGutmanOriginalDegree04ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree05ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree06ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree07ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree08ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree09ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree10ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree11ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree12ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree13ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree14ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree15ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree16ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree17ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree18ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree19ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree20ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree21ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree22ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree23ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree24ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree25ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree26ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree27ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree28ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree29ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree30ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree31ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree32ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree33ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree34ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree35ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree36ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree37ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree38ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree39ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree40ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree41ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree42ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree43ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree44ClassCertificates
import Proofs.RadenkovicGutmanOriginalDegree45ClassCertificates
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeFourToFortyfive
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
theorem certificates (d : ℕ) (h4 : 4≤d) (h45 : d≤45) :
    DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates d := by
  interval_cases d
  · exact OriginalDegree04ClassCertificates.certificates
  · exact OriginalDegree05ClassCertificates.certificates
  · exact OriginalDegree06ClassCertificates.certificates
  · exact OriginalDegree07ClassCertificates.certificates
  · exact OriginalDegree08ClassCertificates.certificates
  · exact OriginalDegree09ClassCertificates.certificates
  · exact OriginalDegree10ClassCertificates.certificates
  · exact OriginalDegree11ClassCertificates.certificates
  · exact OriginalDegree12ClassCertificates.certificates
  · exact OriginalDegree13ClassCertificates.certificates
  · exact OriginalDegree14ClassCertificates.certificates
  · exact OriginalDegree15ClassCertificates.certificates
  · exact OriginalDegree16ClassCertificates.certificates
  · exact OriginalDegree17ClassCertificates.certificates
  · exact OriginalDegree18ClassCertificates.certificates
  · exact OriginalDegree19ClassCertificates.certificates
  · exact OriginalDegree20ClassCertificates.certificates
  · exact OriginalDegree21ClassCertificates.certificates
  · exact OriginalDegree22ClassCertificates.certificates
  · exact OriginalDegree23ClassCertificates.certificates
  · exact OriginalDegree24ClassCertificates.certificates
  · exact OriginalDegree25ClassCertificates.certificates
  · exact OriginalDegree26ClassCertificates.certificates
  · exact OriginalDegree27ClassCertificates.certificates
  · exact OriginalDegree28ClassCertificates.certificates
  · exact OriginalDegree29ClassCertificates.certificates
  · exact OriginalDegree30ClassCertificates.certificates
  · exact OriginalDegree31ClassCertificates.certificates
  · exact OriginalDegree32ClassCertificates.certificates
  · exact OriginalDegree33ClassCertificates.certificates
  · exact OriginalDegree34ClassCertificates.certificates
  · exact OriginalDegree35ClassCertificates.certificates
  · exact OriginalDegree36ClassCertificates.certificates
  · exact OriginalDegree37ClassCertificates.certificates
  · exact OriginalDegree38ClassCertificates.certificates
  · exact OriginalDegree39ClassCertificates.certificates
  · exact OriginalDegree40ClassCertificates.certificates
  · exact OriginalDegree41ClassCertificates.certificates
  · exact OriginalDegree42ClassCertificates.certificates
  · exact OriginalDegree43ClassCertificates.certificates
  · exact OriginalDegree44ClassCertificates.certificates
  · exact OriginalDegree45ClassCertificates.certificates

theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (h4 : 4≤C.degree u) (h45 : C.degree u≤45)
    (h13 : 13≤order C p q) : (2/13 : ℝ)<normalizedIntegral C u p q 2 :=
  DegreeFourToFortyfiveDirectReserveAssembly.input_family certificates m C u p q hT h4 h45 h13
#print axioms certificates
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeFourToFortyfive
