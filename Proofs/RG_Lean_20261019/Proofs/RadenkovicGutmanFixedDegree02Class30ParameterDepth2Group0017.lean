/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0068
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0069
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0070
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0071

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0017
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0068.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0069.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0070.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0071.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/6400),(23/16000),(-7280974047578671336195/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (9/6400) (23/16000) 0 1 0 1 (-7280974047578671336195/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0068.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0069.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0070.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0071.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0017
