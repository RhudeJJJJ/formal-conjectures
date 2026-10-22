/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0030
import Proofs.RadenkovicGutmanD1Long10Cells0031
import Proofs.RadenkovicGutmanD1Long10Cells0032
import Proofs.RadenkovicGutmanD1Long10Cells0033
import Proofs.RadenkovicGutmanD1Long10Cells0034
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk006 : List FastNestedCellData.Cell := [leaf00060,leaf00061,leaf00062,leaf00063,leaf00064,leaf00065,leaf00066,leaf00067,leaf00068,leaf00069]
theorem chunk006_checked : chunk006.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk006
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00060_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00061_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00062_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00063_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00064_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00065_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00066_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00067_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00068_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00069_checked
  rfl
#print axioms chunk006_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
