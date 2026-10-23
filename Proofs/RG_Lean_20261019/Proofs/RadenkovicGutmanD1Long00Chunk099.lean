/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0495
import Proofs.RadenkovicGutmanD1Long00Cells0496
import Proofs.RadenkovicGutmanD1Long00Cells0497
import Proofs.RadenkovicGutmanD1Long00Cells0498
import Proofs.RadenkovicGutmanD1Long00Cells0499
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk099 : List FastNestedCellData.Cell := [leaf00990,leaf00991,leaf00992,leaf00993,leaf00994,leaf00995,leaf00996,leaf00997,leaf00998,leaf00999]
theorem chunk099_checked : chunk099.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk099
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00990_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00991_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00992_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00993_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00994_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00995_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00996_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00997_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00998_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00999_checked
  rfl
#print axioms chunk099_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
