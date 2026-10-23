/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0690
import Proofs.RadenkovicGutmanD1Long00Cells0691
import Proofs.RadenkovicGutmanD1Long00Cells0692
import Proofs.RadenkovicGutmanD1Long00Cells0693
import Proofs.RadenkovicGutmanD1Long00Cells0694
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk138 : List FastNestedCellData.Cell := [leaf01380,leaf01381,leaf01382,leaf01383,leaf01384,leaf01385,leaf01386,leaf01387,leaf01388,leaf01389]
theorem chunk138_checked : chunk138.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk138
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01380_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01381_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01382_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01383_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01384_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01385_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01386_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01387_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01388_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01389_checked
  rfl
#print axioms chunk138_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
