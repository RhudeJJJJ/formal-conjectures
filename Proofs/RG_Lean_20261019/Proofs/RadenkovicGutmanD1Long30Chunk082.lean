/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0410
import Proofs.RadenkovicGutmanD1Long30Cells0411
import Proofs.RadenkovicGutmanD1Long30Cells0412
import Proofs.RadenkovicGutmanD1Long30Cells0413
import Proofs.RadenkovicGutmanD1Long30Cells0414
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk082 : List FastNestedCellData.Cell := [leaf00820,leaf00821,leaf00822,leaf00823,leaf00824,leaf00825,leaf00826,leaf00827,leaf00828,leaf00829]
theorem chunk082_checked : chunk082.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk082
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00820_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00821_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00822_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00823_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00824_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00825_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00826_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00827_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00828_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00829_checked
  rfl
#print axioms chunk082_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
