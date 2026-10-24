/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1284
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1285
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1286
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1287

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0321
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1284.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1285.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1286.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1287.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(291/25600),(73/6400),(-3841463931629742662715/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (291/25600) (73/6400) 0 1 0 1 (-3841463931629742662715/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1284.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1285.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1286.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1287.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0321
