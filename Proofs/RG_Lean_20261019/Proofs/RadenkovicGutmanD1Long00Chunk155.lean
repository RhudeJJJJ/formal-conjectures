/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0775
import Proofs.RadenkovicGutmanD1Long00Cells0776
import Proofs.RadenkovicGutmanD1Long00Cells0777
import Proofs.RadenkovicGutmanD1Long00Cells0778
import Proofs.RadenkovicGutmanD1Long00Cells0779
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk155 : List FastNestedCellData.Cell := [leaf01550,leaf01551,leaf01552,leaf01553,leaf01554,leaf01555,leaf01556,leaf01557,leaf01558,leaf01559]
theorem chunk155_checked : chunk155.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk155
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01550_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01551_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01552_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01553_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01554_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01555_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01556_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01557_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01558_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01559_checked
  rfl
#print axioms chunk155_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
