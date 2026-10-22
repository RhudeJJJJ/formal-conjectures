/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0015
import Proofs.RadenkovicGutmanD1Long10Cells0016
import Proofs.RadenkovicGutmanD1Long10Cells0017
import Proofs.RadenkovicGutmanD1Long10Cells0018
import Proofs.RadenkovicGutmanD1Long10Cells0019
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk003 : List FastNestedCellData.Cell := [leaf00030,leaf00031,leaf00032,leaf00033,leaf00034,leaf00035,leaf00036,leaf00037,leaf00038,leaf00039]
theorem chunk003_checked : chunk003.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk003
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00030_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00031_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00032_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00033_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00034_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00035_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00036_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00037_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00038_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00039_checked
  rfl
#print axioms chunk003_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
