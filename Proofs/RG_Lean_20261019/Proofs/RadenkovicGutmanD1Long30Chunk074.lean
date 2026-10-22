/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0370
import Proofs.RadenkovicGutmanD1Long30Cells0371
import Proofs.RadenkovicGutmanD1Long30Cells0372
import Proofs.RadenkovicGutmanD1Long30Cells0373
import Proofs.RadenkovicGutmanD1Long30Cells0374
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk074 : List FastNestedCellData.Cell := [leaf00740,leaf00741,leaf00742,leaf00743,leaf00744,leaf00745,leaf00746,leaf00747,leaf00748,leaf00749]
theorem chunk074_checked : chunk074.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk074
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00740_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00741_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00742_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00743_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00744_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00745_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00746_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00747_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00748_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00749_checked
  rfl
#print axioms chunk074_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
