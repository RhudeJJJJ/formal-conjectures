/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0620
import Proofs.RadenkovicGutmanD1Long30Cells0621
import Proofs.RadenkovicGutmanD1Long30Cells0622
import Proofs.RadenkovicGutmanD1Long30Cells0623
import Proofs.RadenkovicGutmanD1Long30Cells0624
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk124 : List FastNestedCellData.Cell := [leaf01240,leaf01241,leaf01242,leaf01243,leaf01244,leaf01245,leaf01246,leaf01247,leaf01248,leaf01249]
theorem chunk124_checked : chunk124.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk124
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01240_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01241_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01242_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01243_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01244_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01245_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01246_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01247_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01248_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01249_checked
  rfl
#print axioms chunk124_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
