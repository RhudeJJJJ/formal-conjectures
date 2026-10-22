/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0350
import Proofs.RadenkovicGutmanD1Long30Cells0351
import Proofs.RadenkovicGutmanD1Long30Cells0352
import Proofs.RadenkovicGutmanD1Long30Cells0353
import Proofs.RadenkovicGutmanD1Long30Cells0354
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk070 : List FastNestedCellData.Cell := [leaf00700,leaf00701,leaf00702,leaf00703,leaf00704,leaf00705,leaf00706,leaf00707,leaf00708,leaf00709]
theorem chunk070_checked : chunk070.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk070
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00700_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00701_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00702_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00703_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00704_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00705_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00706_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00707_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00708_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00709_checked
  rfl
#print axioms chunk070_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
