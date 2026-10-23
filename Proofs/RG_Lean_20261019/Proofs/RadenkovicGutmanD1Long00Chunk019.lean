/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0095
import Proofs.RadenkovicGutmanD1Long00Cells0096
import Proofs.RadenkovicGutmanD1Long00Cells0097
import Proofs.RadenkovicGutmanD1Long00Cells0098
import Proofs.RadenkovicGutmanD1Long00Cells0099
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk019 : List FastNestedCellData.Cell := [leaf00190,leaf00191,leaf00192,leaf00193,leaf00194,leaf00195,leaf00196,leaf00197,leaf00198,leaf00199]
theorem chunk019_checked : chunk019.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk019
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00190_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00191_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00192_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00193_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00194_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00195_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00196_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00197_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00198_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00199_checked
  rfl
#print axioms chunk019_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
