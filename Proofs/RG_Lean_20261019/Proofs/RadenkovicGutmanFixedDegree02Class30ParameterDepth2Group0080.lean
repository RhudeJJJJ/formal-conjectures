/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0320
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0321
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0322
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0323

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0080
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0320.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0321.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0322.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0323.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(97/32000),(391/128000),(-11937363885650516142901/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (97/32000) (391/128000) 0 1 0 1 (-11937363885650516142901/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0320.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0321.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0322.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0323.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0080
