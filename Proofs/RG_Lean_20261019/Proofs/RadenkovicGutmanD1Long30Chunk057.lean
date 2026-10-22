/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0285
import Proofs.RadenkovicGutmanD1Long30Cells0286
import Proofs.RadenkovicGutmanD1Long30Cells0287
import Proofs.RadenkovicGutmanD1Long30Cells0288
import Proofs.RadenkovicGutmanD1Long30Cells0289
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk057 : List FastNestedCellData.Cell := [leaf00570,leaf00571,leaf00572,leaf00573,leaf00574,leaf00575,leaf00576,leaf00577,leaf00578,leaf00579]
theorem chunk057_checked : chunk057.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk057
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00570_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00571_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00572_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00573_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00574_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00575_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00576_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00577_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00578_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00579_checked
  rfl
#print axioms chunk057_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
