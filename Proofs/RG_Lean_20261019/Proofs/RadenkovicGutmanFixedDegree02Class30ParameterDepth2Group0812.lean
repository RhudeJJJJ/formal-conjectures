/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3248
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3249
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3250
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3251

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0812
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3248.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3249.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3250.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3251.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(69/1280),(277/5120),(-895543218984359804201/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (69/1280) (277/5120) 0 1 0 1 (-895543218984359804201/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3248.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3249.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3250.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3251.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0812
