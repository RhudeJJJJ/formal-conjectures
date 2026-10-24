/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4056
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4057
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4058
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4059

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1014
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4056.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4057.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4058.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4059.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(39/320),(157/1280),(-925592514816312620265/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (39/320) (157/1280) 0 1 0 1 (-925592514816312620265/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4056.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4057.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4058.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4059.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1014
