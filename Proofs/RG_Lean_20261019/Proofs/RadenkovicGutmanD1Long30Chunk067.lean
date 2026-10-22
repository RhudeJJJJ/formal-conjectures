/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0335
import Proofs.RadenkovicGutmanD1Long30Cells0336
import Proofs.RadenkovicGutmanD1Long30Cells0337
import Proofs.RadenkovicGutmanD1Long30Cells0338
import Proofs.RadenkovicGutmanD1Long30Cells0339
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk067 : List FastNestedCellData.Cell := [leaf00670,leaf00671,leaf00672,leaf00673,leaf00674,leaf00675,leaf00676,leaf00677,leaf00678,leaf00679]
theorem chunk067_checked : chunk067.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk067
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00670_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00671_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00672_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00673_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00674_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00675_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00676_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00677_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00678_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00679_checked
  rfl
#print axioms chunk067_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
