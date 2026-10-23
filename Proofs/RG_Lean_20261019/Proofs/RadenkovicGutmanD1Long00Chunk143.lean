/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0715
import Proofs.RadenkovicGutmanD1Long00Cells0716
import Proofs.RadenkovicGutmanD1Long00Cells0717
import Proofs.RadenkovicGutmanD1Long00Cells0718
import Proofs.RadenkovicGutmanD1Long00Cells0719
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk143 : List FastNestedCellData.Cell := [leaf01430,leaf01431,leaf01432,leaf01433,leaf01434,leaf01435,leaf01436,leaf01437,leaf01438,leaf01439]
theorem chunk143_checked : chunk143.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk143
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01430_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01431_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01432_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01433_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01434_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01435_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01436_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01437_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01438_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01439_checked
  rfl
#print axioms chunk143_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
