/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4888
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4889
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4890
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4891

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1222
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4888.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4889.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4890.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4891.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,16,(512/31),(32612873738712435095/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 16 (512/31) 0 1 0 1 (32612873738712435095/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4888.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4889.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4890.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4891.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1222
