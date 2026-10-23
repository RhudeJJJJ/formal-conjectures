/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0315
import Proofs.RadenkovicGutmanD1Long00Cells0316
import Proofs.RadenkovicGutmanD1Long00Cells0317
import Proofs.RadenkovicGutmanD1Long00Cells0318
import Proofs.RadenkovicGutmanD1Long00Cells0319
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk063 : List FastNestedCellData.Cell := [leaf00630,leaf00631,leaf00632,leaf00633,leaf00634,leaf00635,leaf00636,leaf00637,leaf00638,leaf00639]
theorem chunk063_checked : chunk063.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk063
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00630_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00631_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00632_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00633_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00634_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00635_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00636_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00637_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00638_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00639_checked
  rfl
#print axioms chunk063_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
