/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5060
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5061
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5062
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5063

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1265
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5060.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5061.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5062.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5063.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,128,(2048/15),(3941983665636515/36893488147419103232)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 128 (2048/15) 0 1 0 1 (3941983665636515/36893488147419103232) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf5060.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5061.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf5062.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5063.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1265
