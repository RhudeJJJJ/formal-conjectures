/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0165
import Proofs.RadenkovicGutmanD1Long30Cells0166
import Proofs.RadenkovicGutmanD1Long30Cells0167
import Proofs.RadenkovicGutmanD1Long30Cells0168
import Proofs.RadenkovicGutmanD1Long30Cells0169
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk033 : List FastNestedCellData.Cell := [leaf00330,leaf00331,leaf00332,leaf00333,leaf00334,leaf00335,leaf00336,leaf00337,leaf00338,leaf00339]
theorem chunk033_checked : chunk033.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk033
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00330_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00331_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00332_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00333_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00334_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00335_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00336_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00337_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00338_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00339_checked
  rfl
#print axioms chunk033_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
