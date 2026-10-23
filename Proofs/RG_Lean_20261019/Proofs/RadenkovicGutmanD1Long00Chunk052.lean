/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0260
import Proofs.RadenkovicGutmanD1Long00Cells0261
import Proofs.RadenkovicGutmanD1Long00Cells0262
import Proofs.RadenkovicGutmanD1Long00Cells0263
import Proofs.RadenkovicGutmanD1Long00Cells0264
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk052 : List FastNestedCellData.Cell := [leaf00520,leaf00521,leaf00522,leaf00523,leaf00524,leaf00525,leaf00526,leaf00527,leaf00528,leaf00529]
theorem chunk052_checked : chunk052.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk052
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00520_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00521_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00522_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00523_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00524_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00525_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00526_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00527_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00528_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00529_checked
  rfl
#print axioms chunk052_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
