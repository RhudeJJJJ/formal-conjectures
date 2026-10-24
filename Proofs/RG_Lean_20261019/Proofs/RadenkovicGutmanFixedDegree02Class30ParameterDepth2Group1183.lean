/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4732
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4733
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4734
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4735

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1183
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4732.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4733.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4734.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4735.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/21),(256/41),(184228365776730034627/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (128/21) (256/41) 0 1 0 1 (184228365776730034627/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4732.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4733.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4734.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4735.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1183
