/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0325
import Proofs.RadenkovicGutmanD1Long30Cells0326
import Proofs.RadenkovicGutmanD1Long30Cells0327
import Proofs.RadenkovicGutmanD1Long30Cells0328
import Proofs.RadenkovicGutmanD1Long30Cells0329
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk065 : List FastNestedCellData.Cell := [leaf00650,leaf00651,leaf00652,leaf00653,leaf00654,leaf00655,leaf00656,leaf00657,leaf00658,leaf00659]
theorem chunk065_checked : chunk065.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk065
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00650_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00651_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00652_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00653_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00654_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00655_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00656_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00657_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00658_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00659_checked
  rfl
#print axioms chunk065_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
