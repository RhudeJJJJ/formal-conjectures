/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0415
import Proofs.RadenkovicGutmanD1Long30Cells0416
import Proofs.RadenkovicGutmanD1Long30Cells0417
import Proofs.RadenkovicGutmanD1Long30Cells0418
import Proofs.RadenkovicGutmanD1Long30Cells0419
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk083 : List FastNestedCellData.Cell := [leaf00830,leaf00831,leaf00832,leaf00833,leaf00834,leaf00835,leaf00836,leaf00837,leaf00838,leaf00839]
theorem chunk083_checked : chunk083.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk083
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00830_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00831_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00832_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00833_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00834_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00835_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00836_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00837_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00838_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00839_checked
  rfl
#print axioms chunk083_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
