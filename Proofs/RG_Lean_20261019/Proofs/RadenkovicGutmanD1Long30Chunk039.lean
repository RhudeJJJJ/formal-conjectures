/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0195
import Proofs.RadenkovicGutmanD1Long30Cells0196
import Proofs.RadenkovicGutmanD1Long30Cells0197
import Proofs.RadenkovicGutmanD1Long30Cells0198
import Proofs.RadenkovicGutmanD1Long30Cells0199
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk039 : List FastNestedCellData.Cell := [leaf00390,leaf00391,leaf00392,leaf00393,leaf00394,leaf00395,leaf00396,leaf00397,leaf00398,leaf00399]
theorem chunk039_checked : chunk039.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk039
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00390_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00391_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00392_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00393_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00394_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00395_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00396_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00397_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00398_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00399_checked
  rfl
#print axioms chunk039_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
