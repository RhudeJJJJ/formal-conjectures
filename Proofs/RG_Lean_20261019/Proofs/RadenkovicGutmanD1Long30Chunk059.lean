/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0295
import Proofs.RadenkovicGutmanD1Long30Cells0296
import Proofs.RadenkovicGutmanD1Long30Cells0297
import Proofs.RadenkovicGutmanD1Long30Cells0298
import Proofs.RadenkovicGutmanD1Long30Cells0299
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk059 : List FastNestedCellData.Cell := [leaf00590,leaf00591,leaf00592,leaf00593,leaf00594,leaf00595,leaf00596,leaf00597,leaf00598,leaf00599]
theorem chunk059_checked : chunk059.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk059
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00590_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00591_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00592_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00593_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00594_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00595_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00596_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00597_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00598_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00599_checked
  rfl
#print axioms chunk059_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
