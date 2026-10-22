/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0080
import Proofs.RadenkovicGutmanD1Long30Cells0081
import Proofs.RadenkovicGutmanD1Long30Cells0082
import Proofs.RadenkovicGutmanD1Long30Cells0083
import Proofs.RadenkovicGutmanD1Long30Cells0084
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk016 : List FastNestedCellData.Cell := [leaf00160,leaf00161,leaf00162,leaf00163,leaf00164,leaf00165,leaf00166,leaf00167,leaf00168,leaf00169]
theorem chunk016_checked : chunk016.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk016
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00160_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00161_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00162_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00163_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00164_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00165_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00166_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00167_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00168_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00169_checked
  rfl
#print axioms chunk016_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
