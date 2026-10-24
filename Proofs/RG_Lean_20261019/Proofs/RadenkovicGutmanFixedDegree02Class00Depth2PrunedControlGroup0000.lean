/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf0000
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf0001
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf0002
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf0003
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf0004

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.first (1/4) (.second (1/2) (.second (1/4) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf0000.cell) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf0001.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf0002.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf0003.cell)) (.leaf FixedDegree02Class00Depth2PrunedControlLeaf0004.cell)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/1000),(33/32000),(-32477596038969365167423/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (1/1000) (33/32000) 0 1 0 1 (-32477596038969365167423/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨FixedDegree02Class00Depth2PrunedControlLeaf0000.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf0001.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf0002.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf0003.checked,by decide +kernel,by decide +kernel⟩⟩,⟨FixedDegree02Class00Depth2PrunedControlLeaf0004.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup0000
