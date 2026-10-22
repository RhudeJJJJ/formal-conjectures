/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0340
import Proofs.RadenkovicGutmanD1Long30Cells0341
import Proofs.RadenkovicGutmanD1Long30Cells0342
import Proofs.RadenkovicGutmanD1Long30Cells0343
import Proofs.RadenkovicGutmanD1Long30Cells0344
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk068 : List FastNestedCellData.Cell := [leaf00680,leaf00681,leaf00682,leaf00683,leaf00684,leaf00685,leaf00686,leaf00687,leaf00688,leaf00689]
theorem chunk068_checked : chunk068.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk068
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00680_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00681_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00682_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00683_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00684_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00685_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00686_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00687_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00688_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00689_checked
  rfl
#print axioms chunk068_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
