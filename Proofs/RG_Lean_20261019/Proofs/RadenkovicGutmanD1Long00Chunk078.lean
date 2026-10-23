/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0390
import Proofs.RadenkovicGutmanD1Long00Cells0391
import Proofs.RadenkovicGutmanD1Long00Cells0392
import Proofs.RadenkovicGutmanD1Long00Cells0393
import Proofs.RadenkovicGutmanD1Long00Cells0394
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk078 : List FastNestedCellData.Cell := [leaf00780,leaf00781,leaf00782,leaf00783,leaf00784,leaf00785,leaf00786,leaf00787,leaf00788,leaf00789]
theorem chunk078_checked : chunk078.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk078
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00780_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00781_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00782_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00783_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00784_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00785_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00786_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00787_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00788_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00789_checked
  rfl
#print axioms chunk078_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
