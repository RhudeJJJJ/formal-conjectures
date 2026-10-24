/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0300
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0301
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0302
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0303

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0075
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0300.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0301.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0302.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0303.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(373/128000),(47/16000),(-6035279445731363453505/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (373/128000) (47/16000) 0 1 0 1 (-6035279445731363453505/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0300.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0301.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0302.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0303.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0075
