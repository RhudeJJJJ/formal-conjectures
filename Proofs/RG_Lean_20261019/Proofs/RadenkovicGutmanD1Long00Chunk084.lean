/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0420
import Proofs.RadenkovicGutmanD1Long00Cells0421
import Proofs.RadenkovicGutmanD1Long00Cells0422
import Proofs.RadenkovicGutmanD1Long00Cells0423
import Proofs.RadenkovicGutmanD1Long00Cells0424
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk084 : List FastNestedCellData.Cell := [leaf00840,leaf00841,leaf00842,leaf00843,leaf00844,leaf00845,leaf00846,leaf00847,leaf00848,leaf00849]
theorem chunk084_checked : chunk084.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk084
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00840_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00841_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00842_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00843_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00844_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00845_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00846_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00847_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00848_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00849_checked
  rfl
#print axioms chunk084_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
