/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2272
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2273
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2274
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2275

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0568
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2272.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2273.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2274.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2275.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1297/51200),(13/512),(-1358734466713292769485/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1297/51200) (13/512) 0 1 0 1 (-1358734466713292769485/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2272.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2273.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2274.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2275.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0568
