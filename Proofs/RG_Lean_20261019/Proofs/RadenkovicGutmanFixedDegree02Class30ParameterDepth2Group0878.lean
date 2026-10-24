/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3512
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3513
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3514
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3515

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0878
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3512.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3513.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3514.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3515.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(171/2560),(343/5120),(-1547860062855866928345/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (171/2560) (343/5120) 0 1 0 1 (-1547860062855866928345/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3512.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3513.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3514.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3515.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0878
