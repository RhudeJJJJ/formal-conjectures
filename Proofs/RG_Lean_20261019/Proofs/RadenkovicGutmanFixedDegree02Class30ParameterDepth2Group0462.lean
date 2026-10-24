/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1848
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1849
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1850
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1851

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0462
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1848.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1849.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1850.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1851.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(241/12800),(121/6400),(-6230407359457661000239/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (241/12800) (121/6400) 0 1 0 1 (-6230407359457661000239/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1848.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1849.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1850.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1851.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0462
