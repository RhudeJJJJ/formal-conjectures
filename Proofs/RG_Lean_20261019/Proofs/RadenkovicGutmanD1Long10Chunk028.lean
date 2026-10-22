/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0140
import Proofs.RadenkovicGutmanD1Long10Cells0141
import Proofs.RadenkovicGutmanD1Long10Cells0142
import Proofs.RadenkovicGutmanD1Long10Cells0143
import Proofs.RadenkovicGutmanD1Long10Cells0144
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk028 : List FastNestedCellData.Cell := [leaf00280,leaf00281,leaf00282,leaf00283,leaf00284,leaf00285,leaf00286,leaf00287,leaf00288,leaf00289]
theorem chunk028_checked : chunk028.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk028
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00280_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00281_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00282_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00283_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00284_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00285_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00286_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00287_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00288_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00289_checked
  rfl
#print axioms chunk028_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
