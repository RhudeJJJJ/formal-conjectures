/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0540
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0541
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0542
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0543

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0135
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0540.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0541.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0542.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0543.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(553/128000),(139/32000),(-10752129903982942338685/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (553/128000) (139/32000) 0 1 0 1 (-10752129903982942338685/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0540.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0541.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0542.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0543.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0135
