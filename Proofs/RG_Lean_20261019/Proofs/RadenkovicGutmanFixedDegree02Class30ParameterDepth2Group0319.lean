/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1276
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1277
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1278
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1279

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0319
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1276.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1277.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1278.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1279.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(289/25600),(29/2560),(-3851799088583657902671/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (289/25600) (29/2560) 0 1 0 1 (-3851799088583657902671/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1276.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1277.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1278.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1279.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0319
