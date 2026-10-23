/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0220
import Proofs.RadenkovicGutmanD1Long00Cells0221
import Proofs.RadenkovicGutmanD1Long00Cells0222
import Proofs.RadenkovicGutmanD1Long00Cells0223
import Proofs.RadenkovicGutmanD1Long00Cells0224
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk044 : List FastNestedCellData.Cell := [leaf00440,leaf00441,leaf00442,leaf00443,leaf00444,leaf00445,leaf00446,leaf00447,leaf00448,leaf00449]
theorem chunk044_checked : chunk044.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk044
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00440_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00441_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00442_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00443_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00444_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00445_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00446_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00447_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00448_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00449_checked
  rfl
#print axioms chunk044_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
