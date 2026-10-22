/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0085
import Proofs.RadenkovicGutmanD1Long10Cells0086
import Proofs.RadenkovicGutmanD1Long10Cells0087
import Proofs.RadenkovicGutmanD1Long10Cells0088
import Proofs.RadenkovicGutmanD1Long10Cells0089
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk017 : List FastNestedCellData.Cell := [leaf00170,leaf00171,leaf00172,leaf00173,leaf00174,leaf00175,leaf00176,leaf00177,leaf00178,leaf00179]
theorem chunk017_checked : chunk017.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk017
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00170_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00171_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00172_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00173_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00174_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00175_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00176_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00177_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00178_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00179_checked
  rfl
#print axioms chunk017_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
