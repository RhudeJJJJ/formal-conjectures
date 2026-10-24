/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3048
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3049
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3050
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3051

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0762
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3048.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3049.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3050.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3051.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(119/2560),(1193/25600),(-1964187185321787884743/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (119/2560) (1193/25600) 0 1 0 1 (-1964187185321787884743/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3048.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3049.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3050.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3051.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0762
