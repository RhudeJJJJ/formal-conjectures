/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3860
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3861
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3862
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3863

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0965
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3860.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3861.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3862.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3863.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(121/1280),(243/2560),(-587753439796560356339/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (121/1280) (243/2560) 0 1 0 1 (-587753439796560356339/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3860.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3861.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3862.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3863.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0965
