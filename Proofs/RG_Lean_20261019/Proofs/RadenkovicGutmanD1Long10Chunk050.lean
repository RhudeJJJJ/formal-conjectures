/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0250
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk050 : List FastNestedCellData.Cell := [leaf00500]
theorem chunk050_checked : chunk050.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk050
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00500_checked
  rfl
#print axioms chunk050_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
