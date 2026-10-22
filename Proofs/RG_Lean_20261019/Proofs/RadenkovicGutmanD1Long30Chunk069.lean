/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0345
import Proofs.RadenkovicGutmanD1Long30Cells0346
import Proofs.RadenkovicGutmanD1Long30Cells0347
import Proofs.RadenkovicGutmanD1Long30Cells0348
import Proofs.RadenkovicGutmanD1Long30Cells0349
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk069 : List FastNestedCellData.Cell := [leaf00690,leaf00691,leaf00692,leaf00693,leaf00694,leaf00695,leaf00696,leaf00697,leaf00698,leaf00699]
theorem chunk069_checked : chunk069.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk069
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00690_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00691_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00692_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00693_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00694_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00695_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00696_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00697_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00698_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00699_checked
  rfl
#print axioms chunk069_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
