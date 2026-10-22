/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0100
import Proofs.RadenkovicGutmanD1Long10Cells0101
import Proofs.RadenkovicGutmanD1Long10Cells0102
import Proofs.RadenkovicGutmanD1Long10Cells0103
import Proofs.RadenkovicGutmanD1Long10Cells0104
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk020 : List FastNestedCellData.Cell := [leaf00200,leaf00201,leaf00202,leaf00203,leaf00204,leaf00205,leaf00206,leaf00207,leaf00208,leaf00209]
theorem chunk020_checked : chunk020.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk020
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00200_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00201_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00202_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00203_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00204_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00205_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00206_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00207_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00208_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00209_checked
  rfl
#print axioms chunk020_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
