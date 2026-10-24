/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3364
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3365
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3366
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3367

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0841
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3364.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3365.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3366.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3367.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(61/1024),(153/2560),(-419159362795433632557/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (61/1024) (153/2560) 0 1 0 1 (-419159362795433632557/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3364.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3365.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3366.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3367.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0841
