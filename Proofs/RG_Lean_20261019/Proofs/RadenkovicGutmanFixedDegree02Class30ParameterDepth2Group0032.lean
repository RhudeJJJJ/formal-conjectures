/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0128
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0129
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0130
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0131

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0032
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0128.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0129.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0130.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0131.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/1600),(61/32000),(-6785806287578701712185/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (3/1600) (61/32000) 0 1 0 1 (-6785806287578701712185/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0128.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0129.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0130.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0131.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0032
