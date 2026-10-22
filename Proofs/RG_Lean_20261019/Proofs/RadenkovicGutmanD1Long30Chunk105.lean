/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0525
import Proofs.RadenkovicGutmanD1Long30Cells0526
import Proofs.RadenkovicGutmanD1Long30Cells0527
import Proofs.RadenkovicGutmanD1Long30Cells0528
import Proofs.RadenkovicGutmanD1Long30Cells0529
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk105 : List FastNestedCellData.Cell := [leaf01050,leaf01051,leaf01052,leaf01053,leaf01054,leaf01055,leaf01056,leaf01057,leaf01058,leaf01059]
theorem chunk105_checked : chunk105.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk105
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01050_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01051_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01052_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01053_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01054_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01055_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01056_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01057_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01058_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01059_checked
  rfl
#print axioms chunk105_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
