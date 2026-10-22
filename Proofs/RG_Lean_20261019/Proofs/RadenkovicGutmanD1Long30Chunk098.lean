/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0490
import Proofs.RadenkovicGutmanD1Long30Cells0491
import Proofs.RadenkovicGutmanD1Long30Cells0492
import Proofs.RadenkovicGutmanD1Long30Cells0493
import Proofs.RadenkovicGutmanD1Long30Cells0494
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk098 : List FastNestedCellData.Cell := [leaf00980,leaf00981,leaf00982,leaf00983,leaf00984,leaf00985,leaf00986,leaf00987,leaf00988,leaf00989]
theorem chunk098_checked : chunk098.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk098
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00980_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00981_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00982_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00983_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00984_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00985_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00986_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00987_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00988_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00989_checked
  rfl
#print axioms chunk098_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
