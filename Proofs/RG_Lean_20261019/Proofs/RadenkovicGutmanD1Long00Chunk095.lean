/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0475
import Proofs.RadenkovicGutmanD1Long00Cells0476
import Proofs.RadenkovicGutmanD1Long00Cells0477
import Proofs.RadenkovicGutmanD1Long00Cells0478
import Proofs.RadenkovicGutmanD1Long00Cells0479
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk095 : List FastNestedCellData.Cell := [leaf00950,leaf00951,leaf00952,leaf00953,leaf00954,leaf00955,leaf00956,leaf00957,leaf00958,leaf00959]
theorem chunk095_checked : chunk095.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk095
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00950_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00951_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00952_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00953_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00954_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00955_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00956_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00957_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00958_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00959_checked
  rfl
#print axioms chunk095_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
