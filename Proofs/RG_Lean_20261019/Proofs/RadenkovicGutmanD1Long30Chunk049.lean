/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0245
import Proofs.RadenkovicGutmanD1Long30Cells0246
import Proofs.RadenkovicGutmanD1Long30Cells0247
import Proofs.RadenkovicGutmanD1Long30Cells0248
import Proofs.RadenkovicGutmanD1Long30Cells0249
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk049 : List FastNestedCellData.Cell := [leaf00490,leaf00491,leaf00492,leaf00493,leaf00494,leaf00495,leaf00496,leaf00497,leaf00498,leaf00499]
theorem chunk049_checked : chunk049.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk049
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00490_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00491_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00492_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00493_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00494_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00495_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00496_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00497_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00498_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00499_checked
  rfl
#print axioms chunk049_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
