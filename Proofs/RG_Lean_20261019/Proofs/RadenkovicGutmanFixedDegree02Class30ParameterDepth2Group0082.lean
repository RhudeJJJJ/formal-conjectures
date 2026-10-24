/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0328
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0329
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0330
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0331

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0328.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0329.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0330.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0331.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(197/64000),(397/128000),(-2971396531416530275433/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (197/64000) (397/128000) 0 1 0 1 (-2971396531416530275433/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0328.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0329.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0330.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0331.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0082
