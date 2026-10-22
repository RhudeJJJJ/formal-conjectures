/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0215
import Proofs.RadenkovicGutmanD1Long10Cells0216
import Proofs.RadenkovicGutmanD1Long10Cells0217
import Proofs.RadenkovicGutmanD1Long10Cells0218
import Proofs.RadenkovicGutmanD1Long10Cells0219
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk043 : List FastNestedCellData.Cell := [leaf00430,leaf00431,leaf00432,leaf00433,leaf00434,leaf00435,leaf00436,leaf00437,leaf00438,leaf00439]
theorem chunk043_checked : chunk043.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk043
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00430_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00431_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00432_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00433_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00434_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00435_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00436_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00437_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00438_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00439_checked
  rfl
#print axioms chunk043_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
