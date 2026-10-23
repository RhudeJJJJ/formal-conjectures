/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0035
import Proofs.RadenkovicGutmanD1Long00Cells0036
import Proofs.RadenkovicGutmanD1Long00Cells0037
import Proofs.RadenkovicGutmanD1Long00Cells0038
import Proofs.RadenkovicGutmanD1Long00Cells0039
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk007 : List FastNestedCellData.Cell := [leaf00070,leaf00071,leaf00072,leaf00073,leaf00074,leaf00075,leaf00076,leaf00077,leaf00078,leaf00079]
theorem chunk007_checked : chunk007.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk007
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00070_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00071_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00072_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00073_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00074_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00075_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00076_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00077_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00078_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00079_checked
  rfl
#print axioms chunk007_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
