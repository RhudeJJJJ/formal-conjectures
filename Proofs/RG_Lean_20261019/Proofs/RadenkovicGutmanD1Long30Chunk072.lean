/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0360
import Proofs.RadenkovicGutmanD1Long30Cells0361
import Proofs.RadenkovicGutmanD1Long30Cells0362
import Proofs.RadenkovicGutmanD1Long30Cells0363
import Proofs.RadenkovicGutmanD1Long30Cells0364
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk072 : List FastNestedCellData.Cell := [leaf00720,leaf00721,leaf00722,leaf00723,leaf00724,leaf00725,leaf00726,leaf00727,leaf00728,leaf00729]
theorem chunk072_checked : chunk072.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk072
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00720_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00721_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00722_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00723_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00724_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00725_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00726_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00727_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00728_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00729_checked
  rfl
#print axioms chunk072_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
