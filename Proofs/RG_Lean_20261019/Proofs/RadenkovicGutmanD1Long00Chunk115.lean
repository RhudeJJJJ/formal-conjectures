/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0575
import Proofs.RadenkovicGutmanD1Long00Cells0576
import Proofs.RadenkovicGutmanD1Long00Cells0577
import Proofs.RadenkovicGutmanD1Long00Cells0578
import Proofs.RadenkovicGutmanD1Long00Cells0579
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk115 : List FastNestedCellData.Cell := [leaf01150,leaf01151,leaf01152,leaf01153,leaf01154,leaf01155,leaf01156,leaf01157,leaf01158,leaf01159]
theorem chunk115_checked : chunk115.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk115
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01150_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01151_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01152_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01153_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01154_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01155_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01156_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01157_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01158_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01159_checked
  rfl
#print axioms chunk115_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
