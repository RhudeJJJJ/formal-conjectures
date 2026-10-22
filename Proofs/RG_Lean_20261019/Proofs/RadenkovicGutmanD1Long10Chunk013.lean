/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0065
import Proofs.RadenkovicGutmanD1Long10Cells0066
import Proofs.RadenkovicGutmanD1Long10Cells0067
import Proofs.RadenkovicGutmanD1Long10Cells0068
import Proofs.RadenkovicGutmanD1Long10Cells0069
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk013 : List FastNestedCellData.Cell := [leaf00130,leaf00131,leaf00132,leaf00133,leaf00134,leaf00135,leaf00136,leaf00137,leaf00138,leaf00139]
theorem chunk013_checked : chunk013.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk013
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00130_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00131_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00132_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00133_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00134_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00135_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00136_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00137_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00138_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00139_checked
  rfl
#print axioms chunk013_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
