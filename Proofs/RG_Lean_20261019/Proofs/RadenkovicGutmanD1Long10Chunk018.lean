/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0090
import Proofs.RadenkovicGutmanD1Long10Cells0091
import Proofs.RadenkovicGutmanD1Long10Cells0092
import Proofs.RadenkovicGutmanD1Long10Cells0093
import Proofs.RadenkovicGutmanD1Long10Cells0094
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk018 : List FastNestedCellData.Cell := [leaf00180,leaf00181,leaf00182,leaf00183,leaf00184,leaf00185,leaf00186,leaf00187,leaf00188,leaf00189]
theorem chunk018_checked : chunk018.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk018
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00180_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00181_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00182_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00183_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00184_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00185_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00186_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00187_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00188_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00189_checked
  rfl
#print axioms chunk018_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
