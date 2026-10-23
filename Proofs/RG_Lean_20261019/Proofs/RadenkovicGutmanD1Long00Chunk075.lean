/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0375
import Proofs.RadenkovicGutmanD1Long00Cells0376
import Proofs.RadenkovicGutmanD1Long00Cells0377
import Proofs.RadenkovicGutmanD1Long00Cells0378
import Proofs.RadenkovicGutmanD1Long00Cells0379
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk075 : List FastNestedCellData.Cell := [leaf00750,leaf00751,leaf00752,leaf00753,leaf00754,leaf00755,leaf00756,leaf00757,leaf00758,leaf00759]
theorem chunk075_checked : chunk075.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk075
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00750_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00751_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00752_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00753_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00754_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00755_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00756_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00757_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00758_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00759_checked
  rfl
#print axioms chunk075_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
