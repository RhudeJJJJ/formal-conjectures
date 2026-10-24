/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0024
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0025
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0026
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0027

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0006
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0024.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0025.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0026.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0027.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/6400),(71/64000),(-15439339045429005077399/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (7/6400) (71/64000) 0 1 0 1 (-15439339045429005077399/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0024.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0025.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0026.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0027.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0006
