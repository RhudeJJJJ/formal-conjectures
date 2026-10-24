/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1328
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1329
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1330
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1331

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0332
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1328.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1329.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1330.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1331.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(151/12800),(303/25600),(-15144162873926185454757/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (151/12800) (303/25600) 0 1 0 1 (-15144162873926185454757/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1328.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1329.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1330.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1331.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0332
