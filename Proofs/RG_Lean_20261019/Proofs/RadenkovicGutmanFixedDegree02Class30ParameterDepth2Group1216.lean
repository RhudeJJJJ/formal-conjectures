/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4864
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4865
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4866
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4867

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1216
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4864.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4865.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4866.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4867.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(256/19),(512/37),(22810630622823963153/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (256/19) (512/37) 0 1 0 1 (22810630622823963153/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4864.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4865.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4866.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4867.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1216
