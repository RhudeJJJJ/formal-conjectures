/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0365
import Proofs.RadenkovicGutmanD1Long30Cells0366
import Proofs.RadenkovicGutmanD1Long30Cells0367
import Proofs.RadenkovicGutmanD1Long30Cells0368
import Proofs.RadenkovicGutmanD1Long30Cells0369
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk073 : List FastNestedCellData.Cell := [leaf00730,leaf00731,leaf00732,leaf00733,leaf00734,leaf00735,leaf00736,leaf00737,leaf00738,leaf00739]
theorem chunk073_checked : chunk073.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk073
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00730_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00731_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00732_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00733_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00734_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00735_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00736_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00737_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00738_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00739_checked
  rfl
#print axioms chunk073_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
