/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0205
import Proofs.RadenkovicGutmanD1Long30Cells0206
import Proofs.RadenkovicGutmanD1Long30Cells0207
import Proofs.RadenkovicGutmanD1Long30Cells0208
import Proofs.RadenkovicGutmanD1Long30Cells0209
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk041 : List FastNestedCellData.Cell := [leaf00410,leaf00411,leaf00412,leaf00413,leaf00414,leaf00415,leaf00416,leaf00417,leaf00418,leaf00419]
theorem chunk041_checked : chunk041.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk041
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00410_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00411_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00412_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00413_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00414_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00415_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00416_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00417_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00418_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00419_checked
  rfl
#print axioms chunk041_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
