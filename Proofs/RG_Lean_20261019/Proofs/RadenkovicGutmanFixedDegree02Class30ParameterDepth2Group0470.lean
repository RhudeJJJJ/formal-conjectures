/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1880
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1881
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1882
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1883

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0470
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1880.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1881.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1882.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1883.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(249/12800),(5/256),(-6140745436070537928067/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (249/12800) (5/256) 0 1 0 1 (-6140745436070537928067/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1880.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1881.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1882.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1883.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0470
