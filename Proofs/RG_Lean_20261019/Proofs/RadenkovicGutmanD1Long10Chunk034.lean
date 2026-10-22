/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0170
import Proofs.RadenkovicGutmanD1Long10Cells0171
import Proofs.RadenkovicGutmanD1Long10Cells0172
import Proofs.RadenkovicGutmanD1Long10Cells0173
import Proofs.RadenkovicGutmanD1Long10Cells0174
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk034 : List FastNestedCellData.Cell := [leaf00340,leaf00341,leaf00342,leaf00343,leaf00344,leaf00345,leaf00346,leaf00347,leaf00348,leaf00349]
theorem chunk034_checked : chunk034.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk034
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00340_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00341_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00342_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00343_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00344_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00345_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00346_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00347_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00348_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00349_checked
  rfl
#print axioms chunk034_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
