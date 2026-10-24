/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1936
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1937
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1938
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1939

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0484
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1936.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1937.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1938.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1939.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(209/10240),(131/6400),(-6010015771528870508411/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (209/10240) (131/6400) 0 1 0 1 (-6010015771528870508411/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1936.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1937.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1938.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1939.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0484
