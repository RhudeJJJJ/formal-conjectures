/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0468
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0469
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0470
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0471

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0117
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0468.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0469.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0470.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0471.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(499/128000),(251/64000),(-2773350648074836946673/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (499/128000) (251/64000) 0 1 0 1 (-2773350648074836946673/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0468.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0469.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0470.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0471.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0117
