/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0250
import Proofs.RadenkovicGutmanD1Long30Cells0251
import Proofs.RadenkovicGutmanD1Long30Cells0252
import Proofs.RadenkovicGutmanD1Long30Cells0253
import Proofs.RadenkovicGutmanD1Long30Cells0254
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk050 : List FastNestedCellData.Cell := [leaf00500,leaf00501,leaf00502,leaf00503,leaf00504,leaf00505,leaf00506,leaf00507,leaf00508,leaf00509]
theorem chunk050_checked : chunk050.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk050
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00500_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00501_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00502_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00503_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00504_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00505_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00506_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00507_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00508_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00509_checked
  rfl
#print axioms chunk050_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
