/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0235
import Proofs.RadenkovicGutmanD1Long10Cells0236
import Proofs.RadenkovicGutmanD1Long10Cells0237
import Proofs.RadenkovicGutmanD1Long10Cells0238
import Proofs.RadenkovicGutmanD1Long10Cells0239
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk047 : List FastNestedCellData.Cell := [leaf00470,leaf00471,leaf00472,leaf00473,leaf00474,leaf00475,leaf00476,leaf00477,leaf00478,leaf00479]
theorem chunk047_checked : chunk047.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk047
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00470_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00471_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00472_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00473_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00474_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00475_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00476_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00477_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00478_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00479_checked
  rfl
#print axioms chunk047_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
