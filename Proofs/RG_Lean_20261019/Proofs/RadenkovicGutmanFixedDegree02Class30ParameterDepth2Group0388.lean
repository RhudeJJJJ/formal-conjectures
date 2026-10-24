/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1552
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1553
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1554
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1555

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0388
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1552.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1553.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1554.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1555.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(179/12800),(359/25600),(-7071920496095921896237/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (179/12800) (359/25600) 0 1 0 1 (-7071920496095921896237/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1552.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1553.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1554.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1555.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0388
