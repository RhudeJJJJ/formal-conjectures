/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1856
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1857
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1858
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1859

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0464
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1856.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1857.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1858.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1859.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(243/12800),(61/3200),(-48497391074864447459/18446744073709551616)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (243/12800) (61/3200) 0 1 0 1 (-48497391074864447459/18446744073709551616) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1856.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1857.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1858.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1859.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0464
