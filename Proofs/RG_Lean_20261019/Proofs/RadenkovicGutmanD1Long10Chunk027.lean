/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0135
import Proofs.RadenkovicGutmanD1Long10Cells0136
import Proofs.RadenkovicGutmanD1Long10Cells0137
import Proofs.RadenkovicGutmanD1Long10Cells0138
import Proofs.RadenkovicGutmanD1Long10Cells0139
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk027 : List FastNestedCellData.Cell := [leaf00270,leaf00271,leaf00272,leaf00273,leaf00274,leaf00275,leaf00276,leaf00277,leaf00278,leaf00279]
theorem chunk027_checked : chunk027.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk027
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00270_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00271_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00272_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00273_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00274_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00275_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00276_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00277_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00278_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00279_checked
  rfl
#print axioms chunk027_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
