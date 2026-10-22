/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0515
import Proofs.RadenkovicGutmanD1Long30Cells0516
import Proofs.RadenkovicGutmanD1Long30Cells0517
import Proofs.RadenkovicGutmanD1Long30Cells0518
import Proofs.RadenkovicGutmanD1Long30Cells0519
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk103 : List FastNestedCellData.Cell := [leaf01030,leaf01031,leaf01032,leaf01033,leaf01034,leaf01035,leaf01036,leaf01037,leaf01038,leaf01039]
theorem chunk103_checked : chunk103.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk103
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01030_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01031_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01032_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01033_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01034_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01035_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01036_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01037_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01038_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01039_checked
  rfl
#print axioms chunk103_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
