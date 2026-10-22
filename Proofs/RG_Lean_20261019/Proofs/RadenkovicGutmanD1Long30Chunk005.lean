/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0025
import Proofs.RadenkovicGutmanD1Long30Cells0026
import Proofs.RadenkovicGutmanD1Long30Cells0027
import Proofs.RadenkovicGutmanD1Long30Cells0028
import Proofs.RadenkovicGutmanD1Long30Cells0029
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk005 : List FastNestedCellData.Cell := [leaf00050,leaf00051,leaf00052,leaf00053,leaf00054,leaf00055,leaf00056,leaf00057,leaf00058,leaf00059]
theorem chunk005_checked : chunk005.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk005
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00050_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00051_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00052_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00053_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00054_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00055_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00056_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00057_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00058_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00059_checked
  rfl
#print axioms chunk005_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
