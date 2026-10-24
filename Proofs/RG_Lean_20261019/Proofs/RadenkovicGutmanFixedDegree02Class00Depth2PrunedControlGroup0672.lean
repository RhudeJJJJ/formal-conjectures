/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf3360
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf3361
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf3362
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf3363
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf3364

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup0672
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.first (1/4) (.second (1/2) (.second (1/4) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf3360.cell) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf3361.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf3362.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf3363.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf3364.cell)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(35/1024),(439/12800),(-4636760316574082444283/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (35/1024) (439/12800) 0 1 0 1 (-4636760316574082444283/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨FixedDegree02Class00Depth2PrunedControlLeaf3360.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf3361.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf3362.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf3363.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf3364.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup0672
