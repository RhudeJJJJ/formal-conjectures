/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0155
import Proofs.RadenkovicGutmanD1Long00Cells0156
import Proofs.RadenkovicGutmanD1Long00Cells0157
import Proofs.RadenkovicGutmanD1Long00Cells0158
import Proofs.RadenkovicGutmanD1Long00Cells0159
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk031 : List FastNestedCellData.Cell := [leaf00310,leaf00311,leaf00312,leaf00313,leaf00314,leaf00315,leaf00316,leaf00317,leaf00318,leaf00319]
theorem chunk031_checked : chunk031.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk031
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00310_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00311_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00312_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00313_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00314_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00315_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00316_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00317_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00318_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00319_checked
  rfl
#print axioms chunk031_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
