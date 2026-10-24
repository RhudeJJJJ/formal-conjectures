/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3096
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3097
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3098
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3099

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0774
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3096.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3097.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3098.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3099.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(613/12800),(1229/25600),(-3858085599876598633993/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (613/12800) (1229/25600) 0 1 0 1 (-3858085599876598633993/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3096.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3097.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3098.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3099.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0774
