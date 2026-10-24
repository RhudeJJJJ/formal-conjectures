/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5100
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5101
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5102
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5103

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1275
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5100.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5101.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5102.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5103.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1024/3),(2048/5),(28110383558552551/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1024/3) (2048/5) 0 1 0 1 (28110383558552551/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf5100.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5101.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf5102.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5103.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1275
