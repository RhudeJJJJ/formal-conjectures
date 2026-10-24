/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1928
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1929
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1930
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1931

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0482
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1928.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1929.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1930.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1931.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1039/51200),(521/25600),(-1506413364489731725411/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1039/51200) (521/25600) 0 1 0 1 (-1506413364489731725411/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1928.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1929.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1930.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1931.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0482
