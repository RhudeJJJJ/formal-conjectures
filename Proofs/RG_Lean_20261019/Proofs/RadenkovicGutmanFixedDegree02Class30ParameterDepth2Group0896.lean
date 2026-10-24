/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3584
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3585
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3586
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3587

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0896
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3584.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3585.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3586.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3587.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/128),(361/5120),(-186380893641790800877/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (9/128) (361/5120) 0 1 0 1 (-186380893641790800877/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3584.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3585.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3586.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3587.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0896
