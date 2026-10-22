/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0405
import Proofs.RadenkovicGutmanD1Long30Cells0406
import Proofs.RadenkovicGutmanD1Long30Cells0407
import Proofs.RadenkovicGutmanD1Long30Cells0408
import Proofs.RadenkovicGutmanD1Long30Cells0409
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk081 : List FastNestedCellData.Cell := [leaf00810,leaf00811,leaf00812,leaf00813,leaf00814,leaf00815,leaf00816,leaf00817,leaf00818,leaf00819]
theorem chunk081_checked : chunk081.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk081
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00810_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00811_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00812_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00813_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00814_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00815_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00816_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00817_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00818_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00819_checked
  rfl
#print axioms chunk081_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
