/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0545
import Proofs.RadenkovicGutmanD1Long00Cells0546
import Proofs.RadenkovicGutmanD1Long00Cells0547
import Proofs.RadenkovicGutmanD1Long00Cells0548
import Proofs.RadenkovicGutmanD1Long00Cells0549
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk109 : List FastNestedCellData.Cell := [leaf01090,leaf01091,leaf01092,leaf01093,leaf01094,leaf01095,leaf01096,leaf01097,leaf01098,leaf01099]
theorem chunk109_checked : chunk109.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk109
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01090_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01091_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01092_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01093_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01094_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01095_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01096_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01097_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01098_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01099_checked
  rfl
#print axioms chunk109_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
