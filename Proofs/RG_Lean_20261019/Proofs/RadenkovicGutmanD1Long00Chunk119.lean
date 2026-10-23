/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0595
import Proofs.RadenkovicGutmanD1Long00Cells0596
import Proofs.RadenkovicGutmanD1Long00Cells0597
import Proofs.RadenkovicGutmanD1Long00Cells0598
import Proofs.RadenkovicGutmanD1Long00Cells0599
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk119 : List FastNestedCellData.Cell := [leaf01190,leaf01191,leaf01192,leaf01193,leaf01194,leaf01195,leaf01196,leaf01197,leaf01198,leaf01199]
theorem chunk119_checked : chunk119.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk119
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01190_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01191_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01192_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01193_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01194_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01195_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01196_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01197_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01198_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01199_checked
  rfl
#print axioms chunk119_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
