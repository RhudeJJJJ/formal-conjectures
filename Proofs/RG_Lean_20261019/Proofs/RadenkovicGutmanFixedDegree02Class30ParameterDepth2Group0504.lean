/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2016
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2017
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2018
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2019

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0504
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2016.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2017.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2018.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2019.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(221/10240),(277/12800),(-2929621975140001805191/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (221/10240) (277/12800) 0 1 0 1 (-2929621975140001805191/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2016.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2017.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2018.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2019.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0504
