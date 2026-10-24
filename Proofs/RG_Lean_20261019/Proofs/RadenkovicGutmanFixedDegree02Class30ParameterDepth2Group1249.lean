/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4996
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4997
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4998
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4999

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1249
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4996.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4997.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4998.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4999.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1024/23),(512/11),(268541124419682885/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1024/23) (512/11) 0 1 0 1 (268541124419682885/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4996.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4997.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4998.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4999.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1249
