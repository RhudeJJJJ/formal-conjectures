/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0300
import Proofs.RadenkovicGutmanD1Long00Cells0301
import Proofs.RadenkovicGutmanD1Long00Cells0302
import Proofs.RadenkovicGutmanD1Long00Cells0303
import Proofs.RadenkovicGutmanD1Long00Cells0304
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk060 : List FastNestedCellData.Cell := [leaf00600,leaf00601,leaf00602,leaf00603,leaf00604,leaf00605,leaf00606,leaf00607,leaf00608,leaf00609]
theorem chunk060_checked : chunk060.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk060
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00600_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00601_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00602_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00603_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00604_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00605_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00606_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00607_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00608_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00609_checked
  rfl
#print axioms chunk060_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
