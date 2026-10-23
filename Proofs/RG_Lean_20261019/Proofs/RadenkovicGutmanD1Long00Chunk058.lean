/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0290
import Proofs.RadenkovicGutmanD1Long00Cells0291
import Proofs.RadenkovicGutmanD1Long00Cells0292
import Proofs.RadenkovicGutmanD1Long00Cells0293
import Proofs.RadenkovicGutmanD1Long00Cells0294
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk058 : List FastNestedCellData.Cell := [leaf00580,leaf00581,leaf00582,leaf00583,leaf00584,leaf00585,leaf00586,leaf00587,leaf00588,leaf00589]
theorem chunk058_checked : chunk058.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk058
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00580_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00581_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00582_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00583_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00584_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00585_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00586_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00587_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00588_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00589_checked
  rfl
#print axioms chunk058_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
