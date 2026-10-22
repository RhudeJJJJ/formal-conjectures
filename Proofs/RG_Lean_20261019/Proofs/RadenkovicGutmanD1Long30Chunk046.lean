/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0230
import Proofs.RadenkovicGutmanD1Long30Cells0231
import Proofs.RadenkovicGutmanD1Long30Cells0232
import Proofs.RadenkovicGutmanD1Long30Cells0233
import Proofs.RadenkovicGutmanD1Long30Cells0234
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk046 : List FastNestedCellData.Cell := [leaf00460,leaf00461,leaf00462,leaf00463,leaf00464,leaf00465,leaf00466,leaf00467,leaf00468,leaf00469]
theorem chunk046_checked : chunk046.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk046
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00460_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00461_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00462_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00463_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00464_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00465_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00466_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00467_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00468_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00469_checked
  rfl
#print axioms chunk046_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
