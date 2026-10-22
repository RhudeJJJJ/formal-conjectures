/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0425
import Proofs.RadenkovicGutmanD1Long30Cells0426
import Proofs.RadenkovicGutmanD1Long30Cells0427
import Proofs.RadenkovicGutmanD1Long30Cells0428
import Proofs.RadenkovicGutmanD1Long30Cells0429
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk085 : List FastNestedCellData.Cell := [leaf00850,leaf00851,leaf00852,leaf00853,leaf00854,leaf00855,leaf00856,leaf00857,leaf00858,leaf00859]
theorem chunk085_checked : chunk085.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk085
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00850_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00851_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00852_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00853_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00854_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00855_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00856_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00857_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00858_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00859_checked
  rfl
#print axioms chunk085_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
