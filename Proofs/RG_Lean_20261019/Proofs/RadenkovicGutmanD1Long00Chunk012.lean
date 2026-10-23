/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0060
import Proofs.RadenkovicGutmanD1Long00Cells0061
import Proofs.RadenkovicGutmanD1Long00Cells0062
import Proofs.RadenkovicGutmanD1Long00Cells0063
import Proofs.RadenkovicGutmanD1Long00Cells0064
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk012 : List FastNestedCellData.Cell := [leaf00120,leaf00121,leaf00122,leaf00123,leaf00124,leaf00125,leaf00126,leaf00127,leaf00128,leaf00129]
theorem chunk012_checked : chunk012.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk012
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00120_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00121_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00122_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00123_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00124_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00125_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00126_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00127_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00128_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00129_checked
  rfl
#print axioms chunk012_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
