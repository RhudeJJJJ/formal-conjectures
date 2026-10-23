/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0655
import Proofs.RadenkovicGutmanD1Long00Cells0656
import Proofs.RadenkovicGutmanD1Long00Cells0657
import Proofs.RadenkovicGutmanD1Long00Cells0658
import Proofs.RadenkovicGutmanD1Long00Cells0659
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk131 : List FastNestedCellData.Cell := [leaf01310,leaf01311,leaf01312,leaf01313,leaf01314,leaf01315,leaf01316,leaf01317,leaf01318,leaf01319]
theorem chunk131_checked : chunk131.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk131
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01310_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01311_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01312_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01313_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01314_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01315_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01316_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01317_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01318_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01319_checked
  rfl
#print axioms chunk131_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
