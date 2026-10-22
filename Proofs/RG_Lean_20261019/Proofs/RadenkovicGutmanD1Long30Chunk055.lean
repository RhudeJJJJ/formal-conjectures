/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0275
import Proofs.RadenkovicGutmanD1Long30Cells0276
import Proofs.RadenkovicGutmanD1Long30Cells0277
import Proofs.RadenkovicGutmanD1Long30Cells0278
import Proofs.RadenkovicGutmanD1Long30Cells0279
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk055 : List FastNestedCellData.Cell := [leaf00550,leaf00551,leaf00552,leaf00553,leaf00554,leaf00555,leaf00556,leaf00557,leaf00558,leaf00559]
theorem chunk055_checked : chunk055.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk055
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00550_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00551_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00552_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00553_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00554_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00555_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00556_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00557_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00558_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00559_checked
  rfl
#print axioms chunk055_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
