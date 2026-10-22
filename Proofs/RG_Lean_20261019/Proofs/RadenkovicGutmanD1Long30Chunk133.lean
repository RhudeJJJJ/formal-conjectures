/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0665
import Proofs.RadenkovicGutmanD1Long30Cells0666
import Proofs.RadenkovicGutmanD1Long30Cells0667
import Proofs.RadenkovicGutmanD1Long30Cells0668
import Proofs.RadenkovicGutmanD1Long30Cells0669
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk133 : List FastNestedCellData.Cell := [leaf01330,leaf01331,leaf01332,leaf01333,leaf01334,leaf01335,leaf01336,leaf01337,leaf01338,leaf01339]
theorem chunk133_checked : chunk133.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk133
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01330_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01331_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01332_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01333_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01334_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01335_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01336_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01337_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01338_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01339_checked
  rfl
#print axioms chunk133_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
