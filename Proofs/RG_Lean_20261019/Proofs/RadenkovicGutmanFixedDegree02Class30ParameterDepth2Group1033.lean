/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4132
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4133
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4134
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4135

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1033
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4132.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4133.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4134.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4135.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(35/256),(11/80),(-1641199901188504852379/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (35/256) (11/80) 0 1 0 1 (-1641199901188504852379/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4132.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4133.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4134.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4135.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1033
