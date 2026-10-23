/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0380
import Proofs.RadenkovicGutmanD1Long00Cells0381
import Proofs.RadenkovicGutmanD1Long00Cells0382
import Proofs.RadenkovicGutmanD1Long00Cells0383
import Proofs.RadenkovicGutmanD1Long00Cells0384
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk076 : List FastNestedCellData.Cell := [leaf00760,leaf00761,leaf00762,leaf00763,leaf00764,leaf00765,leaf00766,leaf00767,leaf00768,leaf00769]
theorem chunk076_checked : chunk076.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk076
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00760_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00761_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00762_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00763_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00764_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00765_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00766_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00767_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00768_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00769_checked
  rfl
#print axioms chunk076_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
