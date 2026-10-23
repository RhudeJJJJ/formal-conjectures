/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0480
import Proofs.RadenkovicGutmanD1Long00Cells0481
import Proofs.RadenkovicGutmanD1Long00Cells0482
import Proofs.RadenkovicGutmanD1Long00Cells0483
import Proofs.RadenkovicGutmanD1Long00Cells0484
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk096 : List FastNestedCellData.Cell := [leaf00960,leaf00961,leaf00962,leaf00963,leaf00964,leaf00965,leaf00966,leaf00967,leaf00968,leaf00969]
theorem chunk096_checked : chunk096.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk096
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00960_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00961_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00962_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00963_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00964_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00965_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00966_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00967_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00968_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00969_checked
  rfl
#print axioms chunk096_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
