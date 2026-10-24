/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3380
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3381
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3382
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3383

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0845
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3380.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3381.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3382.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3383.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(309/5120),(31/512),(-1661851936924987287493/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (309/5120) (31/512) 0 1 0 1 (-1661851936924987287493/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3380.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3381.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3382.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3383.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0845
