/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0225
import Proofs.RadenkovicGutmanD1Long00Cells0226
import Proofs.RadenkovicGutmanD1Long00Cells0227
import Proofs.RadenkovicGutmanD1Long00Cells0228
import Proofs.RadenkovicGutmanD1Long00Cells0229
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk045 : List FastNestedCellData.Cell := [leaf00450,leaf00451,leaf00452,leaf00453,leaf00454,leaf00455,leaf00456,leaf00457,leaf00458,leaf00459]
theorem chunk045_checked : chunk045.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk045
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00450_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00451_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00452_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00453_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00454_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00455_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00456_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00457_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00458_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00459_checked
  rfl
#print axioms chunk045_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
