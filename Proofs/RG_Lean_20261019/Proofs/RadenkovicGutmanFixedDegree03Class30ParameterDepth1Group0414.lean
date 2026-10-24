/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0828
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0829

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0414
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0828.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0829.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(131/640),(67/320),(-504157972382214407819/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (131/640) (67/320) 0 1 0 1 (-504157972382214407819/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0828.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0829.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0414
