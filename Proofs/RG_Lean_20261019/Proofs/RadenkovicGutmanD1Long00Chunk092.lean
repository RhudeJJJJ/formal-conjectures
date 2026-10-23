/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0460
import Proofs.RadenkovicGutmanD1Long00Cells0461
import Proofs.RadenkovicGutmanD1Long00Cells0462
import Proofs.RadenkovicGutmanD1Long00Cells0463
import Proofs.RadenkovicGutmanD1Long00Cells0464
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk092 : List FastNestedCellData.Cell := [leaf00920,leaf00921,leaf00922,leaf00923,leaf00924,leaf00925,leaf00926,leaf00927,leaf00928,leaf00929]
theorem chunk092_checked : chunk092.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk092
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00920_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00921_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00922_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00923_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00924_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00925_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00926_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00927_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00928_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00929_checked
  rfl
#print axioms chunk092_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
