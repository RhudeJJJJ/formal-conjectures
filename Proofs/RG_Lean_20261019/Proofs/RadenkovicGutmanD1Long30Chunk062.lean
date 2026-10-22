/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0310
import Proofs.RadenkovicGutmanD1Long30Cells0311
import Proofs.RadenkovicGutmanD1Long30Cells0312
import Proofs.RadenkovicGutmanD1Long30Cells0313
import Proofs.RadenkovicGutmanD1Long30Cells0314
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk062 : List FastNestedCellData.Cell := [leaf00620,leaf00621,leaf00622,leaf00623,leaf00624,leaf00625,leaf00626,leaf00627,leaf00628,leaf00629]
theorem chunk062_checked : chunk062.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk062
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00620_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00621_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00622_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00623_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00624_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00625_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00626_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00627_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00628_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00629_checked
  rfl
#print axioms chunk062_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
