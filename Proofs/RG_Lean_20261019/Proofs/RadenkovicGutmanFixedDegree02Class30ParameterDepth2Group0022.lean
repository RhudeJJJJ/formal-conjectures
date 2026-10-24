/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0088
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0089
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0090
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0091

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0022
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0088.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0089.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0090.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0091.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/640),(51/32000),(-28397065921892493038817/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1/640) (51/32000) 0 1 0 1 (-28397065921892493038817/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0088.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0089.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0090.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0091.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0022
