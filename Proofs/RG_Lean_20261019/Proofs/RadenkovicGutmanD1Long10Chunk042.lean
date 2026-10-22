/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0210
import Proofs.RadenkovicGutmanD1Long10Cells0211
import Proofs.RadenkovicGutmanD1Long10Cells0212
import Proofs.RadenkovicGutmanD1Long10Cells0213
import Proofs.RadenkovicGutmanD1Long10Cells0214
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk042 : List FastNestedCellData.Cell := [leaf00420,leaf00421,leaf00422,leaf00423,leaf00424,leaf00425,leaf00426,leaf00427,leaf00428,leaf00429]
theorem chunk042_checked : chunk042.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk042
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00420_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00421_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00422_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00423_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00424_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00425_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00426_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00427_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00428_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00429_checked
  rfl
#print axioms chunk042_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
