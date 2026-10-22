/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0120
import Proofs.RadenkovicGutmanD1Long10Cells0121
import Proofs.RadenkovicGutmanD1Long10Cells0122
import Proofs.RadenkovicGutmanD1Long10Cells0123
import Proofs.RadenkovicGutmanD1Long10Cells0124
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk024 : List FastNestedCellData.Cell := [leaf00240,leaf00241,leaf00242,leaf00243,leaf00244,leaf00245,leaf00246,leaf00247,leaf00248,leaf00249]
theorem chunk024_checked : chunk024.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk024
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00240_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00241_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00242_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00243_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00244_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00245_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00246_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00247_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00248_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00249_checked
  rfl
#print axioms chunk024_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
