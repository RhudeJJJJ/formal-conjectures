/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2368
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2369
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2370
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2371

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0592
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2368.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2369.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2370.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2371.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1369/51200),(343/12800),(-5294572148951274995345/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1369/51200) (343/12800) 0 1 0 1 (-5294572148951274995345/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2368.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2369.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2370.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2371.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0592
