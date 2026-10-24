/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4700
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4701
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4702
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4703

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1175
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4700.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4701.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4702.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4703.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/25),(256/49),(120193083032006391975/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (128/25) (256/49) 0 1 0 1 (120193083032006391975/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4700.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4701.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4702.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4703.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1175
