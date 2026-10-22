/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0535
import Proofs.RadenkovicGutmanD1Long30Cells0536
import Proofs.RadenkovicGutmanD1Long30Cells0537
import Proofs.RadenkovicGutmanD1Long30Cells0538
import Proofs.RadenkovicGutmanD1Long30Cells0539
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk107 : List FastNestedCellData.Cell := [leaf01070,leaf01071,leaf01072,leaf01073,leaf01074,leaf01075,leaf01076,leaf01077,leaf01078,leaf01079]
theorem chunk107_checked : chunk107.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk107
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01070_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01071_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01072_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01073_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01074_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01075_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01076_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01077_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01078_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01079_checked
  rfl
#print axioms chunk107_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
