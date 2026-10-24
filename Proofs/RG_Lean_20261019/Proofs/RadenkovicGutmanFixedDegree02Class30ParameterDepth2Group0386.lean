/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1544
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1545
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1546
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1547

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0386
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1544.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1545.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1546.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1547.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(89/6400),(357/25600),(-7088177370505277734683/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (89/6400) (357/25600) 0 1 0 1 (-7088177370505277734683/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1544.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1545.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1546.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1547.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0386
