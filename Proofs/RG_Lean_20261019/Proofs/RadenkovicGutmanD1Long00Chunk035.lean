/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0175
import Proofs.RadenkovicGutmanD1Long00Cells0176
import Proofs.RadenkovicGutmanD1Long00Cells0177
import Proofs.RadenkovicGutmanD1Long00Cells0178
import Proofs.RadenkovicGutmanD1Long00Cells0179
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk035 : List FastNestedCellData.Cell := [leaf00350,leaf00351,leaf00352,leaf00353,leaf00354,leaf00355,leaf00356,leaf00357,leaf00358,leaf00359]
theorem chunk035_checked : chunk035.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk035
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00350_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00351_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00352_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00353_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00354_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00355_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00356_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00357_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00358_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00359_checked
  rfl
#print axioms chunk035_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
