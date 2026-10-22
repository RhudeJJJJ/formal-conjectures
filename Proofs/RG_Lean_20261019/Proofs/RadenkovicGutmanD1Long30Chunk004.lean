/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0020
import Proofs.RadenkovicGutmanD1Long30Cells0021
import Proofs.RadenkovicGutmanD1Long30Cells0022
import Proofs.RadenkovicGutmanD1Long30Cells0023
import Proofs.RadenkovicGutmanD1Long30Cells0024
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk004 : List FastNestedCellData.Cell := [leaf00040,leaf00041,leaf00042,leaf00043,leaf00044,leaf00045,leaf00046,leaf00047,leaf00048,leaf00049]
theorem chunk004_checked : chunk004.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk004
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00040_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00041_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00042_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00043_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00044_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00045_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00046_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00047_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00048_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00049_checked
  rfl
#print axioms chunk004_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
