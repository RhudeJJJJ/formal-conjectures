/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4976
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4977
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4978
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4979

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1244
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4976.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4977.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4978.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4979.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(256/7),(1024/27),(1610911050396893593/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (256/7) (1024/27) 0 1 0 1 (1610911050396893593/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4976.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4977.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4978.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4979.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1244
