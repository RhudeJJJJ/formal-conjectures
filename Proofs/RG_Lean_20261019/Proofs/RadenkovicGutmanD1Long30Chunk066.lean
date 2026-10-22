/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0330
import Proofs.RadenkovicGutmanD1Long30Cells0331
import Proofs.RadenkovicGutmanD1Long30Cells0332
import Proofs.RadenkovicGutmanD1Long30Cells0333
import Proofs.RadenkovicGutmanD1Long30Cells0334
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk066 : List FastNestedCellData.Cell := [leaf00660,leaf00661,leaf00662,leaf00663,leaf00664,leaf00665,leaf00666,leaf00667,leaf00668,leaf00669]
theorem chunk066_checked : chunk066.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk066
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00660_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00661_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00662_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00663_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00664_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00665_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00666_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00667_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00668_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00669_checked
  rfl
#print axioms chunk066_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
