/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0956
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0957
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0958
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0959

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0239
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0956.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0957.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0958.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0959.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(209/25600),(21/2560),(-8697141981747463427157/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (209/25600) (21/2560) 0 1 0 1 (-8697141981747463427157/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0956.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0957.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0958.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0959.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0239
