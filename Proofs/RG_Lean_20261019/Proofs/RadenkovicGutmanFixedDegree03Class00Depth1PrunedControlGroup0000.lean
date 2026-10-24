/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf0000
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf0001
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf0002
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf0003

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class00Depth1PrunedControlGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf0000.cell) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf0001.cell)) (.second (1/2) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf0002.cell) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf0003.cell))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/1000),(33/32000),(-34043390199624400115565/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 3 4 4 (1/1000) (33/32000) 0 1 0 1 (-34043390199624400115565/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree03Class00Depth1PrunedControlLeaf0000.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class00Depth1PrunedControlLeaf0001.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree03Class00Depth1PrunedControlLeaf0002.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class00Depth1PrunedControlLeaf0003.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class00Depth1PrunedControlGroup0000
