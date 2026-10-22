/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0070
import Proofs.RadenkovicGutmanD1Long10Cells0071
import Proofs.RadenkovicGutmanD1Long10Cells0072
import Proofs.RadenkovicGutmanD1Long10Cells0073
import Proofs.RadenkovicGutmanD1Long10Cells0074
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk014 : List FastNestedCellData.Cell := [leaf00140,leaf00141,leaf00142,leaf00143,leaf00144,leaf00145,leaf00146,leaf00147,leaf00148,leaf00149]
theorem chunk014_checked : chunk014.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk014
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00140_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00141_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00142_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00143_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00144_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00145_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00146_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00147_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00148_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00149_checked
  rfl
#print axioms chunk014_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
