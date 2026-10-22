/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0440
import Proofs.RadenkovicGutmanD1Long30Cells0441
import Proofs.RadenkovicGutmanD1Long30Cells0442
import Proofs.RadenkovicGutmanD1Long30Cells0443
import Proofs.RadenkovicGutmanD1Long30Cells0444
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk088 : List FastNestedCellData.Cell := [leaf00880,leaf00881,leaf00882,leaf00883,leaf00884,leaf00885,leaf00886,leaf00887,leaf00888,leaf00889]
theorem chunk088_checked : chunk088.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk088
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00880_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00881_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00882_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00883_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00884_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00885_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00886_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00887_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00888_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00889_checked
  rfl
#print axioms chunk088_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
