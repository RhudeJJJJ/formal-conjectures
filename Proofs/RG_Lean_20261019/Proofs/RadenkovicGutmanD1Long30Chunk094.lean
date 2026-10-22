/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0470
import Proofs.RadenkovicGutmanD1Long30Cells0471
import Proofs.RadenkovicGutmanD1Long30Cells0472
import Proofs.RadenkovicGutmanD1Long30Cells0473
import Proofs.RadenkovicGutmanD1Long30Cells0474
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk094 : List FastNestedCellData.Cell := [leaf00940,leaf00941,leaf00942,leaf00943,leaf00944,leaf00945,leaf00946,leaf00947,leaf00948,leaf00949]
theorem chunk094_checked : chunk094.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk094
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00940_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00941_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00942_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00943_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00944_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00945_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00946_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00947_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00948_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00949_checked
  rfl
#print axioms chunk094_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
