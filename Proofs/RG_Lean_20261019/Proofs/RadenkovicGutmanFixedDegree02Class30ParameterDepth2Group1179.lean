/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4716
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4717
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4718
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4719

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1179
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4716.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4717.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4718.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4719.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/23),(256/45),(106178588999866767275/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (128/23) (256/45) 0 1 0 1 (106178588999866767275/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4716.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4717.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4718.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4719.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1179
