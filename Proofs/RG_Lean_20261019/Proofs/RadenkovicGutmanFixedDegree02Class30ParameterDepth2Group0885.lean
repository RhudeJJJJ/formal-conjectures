/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3540
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3541
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3542
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3543

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0885
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3540.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3541.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3542.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3543.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(349/5120),(35/512),(-1525351374165082533639/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (349/5120) (35/512) 0 1 0 1 (-1525351374165082533639/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3540.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3541.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3542.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3543.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0885
