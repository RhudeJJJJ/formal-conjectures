/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0465
import Proofs.RadenkovicGutmanD1Long30Cells0466
import Proofs.RadenkovicGutmanD1Long30Cells0467
import Proofs.RadenkovicGutmanD1Long30Cells0468
import Proofs.RadenkovicGutmanD1Long30Cells0469
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk093 : List FastNestedCellData.Cell := [leaf00930,leaf00931,leaf00932,leaf00933,leaf00934,leaf00935,leaf00936,leaf00937,leaf00938,leaf00939]
theorem chunk093_checked : chunk093.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk093
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00930_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00931_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00932_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00933_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00934_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00935_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00936_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00937_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00938_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00939_checked
  rfl
#print axioms chunk093_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
