/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0055
import Proofs.RadenkovicGutmanD1Long00Cells0056
import Proofs.RadenkovicGutmanD1Long00Cells0057
import Proofs.RadenkovicGutmanD1Long00Cells0058
import Proofs.RadenkovicGutmanD1Long00Cells0059
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk011 : List FastNestedCellData.Cell := [leaf00110,leaf00111,leaf00112,leaf00113,leaf00114,leaf00115,leaf00116,leaf00117,leaf00118,leaf00119]
theorem chunk011_checked : chunk011.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk011
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00110_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00111_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00112_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00113_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00114_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00115_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00116_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00117_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00118_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00119_checked
  rfl
#print axioms chunk011_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
