/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0232
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0233
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0234
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0235

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0232.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0233.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0234.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0235.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(161/64000),(13/5120),(-12569202993267824484777/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (161/64000) (13/5120) 0 1 0 1 (-12569202993267824484777/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0232.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0233.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0234.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0235.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0058
