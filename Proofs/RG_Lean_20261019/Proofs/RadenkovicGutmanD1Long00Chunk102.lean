/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0510
import Proofs.RadenkovicGutmanD1Long00Cells0511
import Proofs.RadenkovicGutmanD1Long00Cells0512
import Proofs.RadenkovicGutmanD1Long00Cells0513
import Proofs.RadenkovicGutmanD1Long00Cells0514
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk102 : List FastNestedCellData.Cell := [leaf01020,leaf01021,leaf01022,leaf01023,leaf01024,leaf01025,leaf01026,leaf01027,leaf01028,leaf01029]
theorem chunk102_checked : chunk102.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk102
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01020_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01021_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01022_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01023_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01024_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01025_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01026_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01027_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01028_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01029_checked
  rfl
#print axioms chunk102_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
