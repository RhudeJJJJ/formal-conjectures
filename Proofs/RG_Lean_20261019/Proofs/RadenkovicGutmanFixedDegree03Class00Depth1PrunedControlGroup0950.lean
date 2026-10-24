/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf3800
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf3801
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf3802
import Proofs.RadenkovicGutmanFixedDegree03Class00Depth1PrunedControlLeaf3803

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class00Depth1PrunedControlGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf3800.cell) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf3801.cell)) (.second (1/2) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf3802.cell) (.leaf FixedDegree03Class00Depth1PrunedControlLeaf3803.cell))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(4096/5),1024,(3375902963881781/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 3 4 4 (4096/5) 1024 0 1 0 1 (3375902963881781/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree03Class00Depth1PrunedControlLeaf3800.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class00Depth1PrunedControlLeaf3801.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree03Class00Depth1PrunedControlLeaf3802.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class00Depth1PrunedControlLeaf3803.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class00Depth1PrunedControlGroup0950
