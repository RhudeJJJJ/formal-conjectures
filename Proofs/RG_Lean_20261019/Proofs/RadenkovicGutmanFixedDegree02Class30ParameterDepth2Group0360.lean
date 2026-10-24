/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1440
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1441
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1442
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1443

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0360
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1440.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1441.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1442.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1443.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(33/2560),(331/25600),(-1827426605807548168437/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (33/2560) (331/25600) 0 1 0 1 (-1827426605807548168437/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1440.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1441.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1442.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1443.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0360
