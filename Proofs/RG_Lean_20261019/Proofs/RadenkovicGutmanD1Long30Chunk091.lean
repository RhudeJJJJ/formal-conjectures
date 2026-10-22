/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0455
import Proofs.RadenkovicGutmanD1Long30Cells0456
import Proofs.RadenkovicGutmanD1Long30Cells0457
import Proofs.RadenkovicGutmanD1Long30Cells0458
import Proofs.RadenkovicGutmanD1Long30Cells0459
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk091 : List FastNestedCellData.Cell := [leaf00910,leaf00911,leaf00912,leaf00913,leaf00914,leaf00915,leaf00916,leaf00917,leaf00918,leaf00919]
theorem chunk091_checked : chunk091.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk091
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00910_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00911_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00912_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00913_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00914_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00915_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00916_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00917_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00918_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00919_checked
  rfl
#print axioms chunk091_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
