/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0354
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0355

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0177
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0354.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0355.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(319/12800),(161/6400),(-180779365903304913613/73786976294838206464)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (319/12800) (161/6400) 0 1 0 1 (-180779365903304913613/73786976294838206464) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0354.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0355.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0177
