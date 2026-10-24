/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3936
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3937
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3938
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3939

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0984
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3936.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3937.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3938.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3939.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(261/2560),(131/1280),(-1098845206089815429683/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (261/2560) (131/1280) 0 1 0 1 (-1098845206089815429683/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3936.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3937.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3938.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3939.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0984
