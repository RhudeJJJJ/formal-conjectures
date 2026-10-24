/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2768
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2769
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2770
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2771

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0692
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2768.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2769.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2770.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2771.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(49/1280),(983/25600),(-1098558383262464107713/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (49/1280) (983/25600) 0 1 0 1 (-1098558383262464107713/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2768.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2769.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2770.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2771.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0692
