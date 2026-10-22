/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0550
import Proofs.RadenkovicGutmanD1Long30Cells0551
import Proofs.RadenkovicGutmanD1Long30Cells0552
import Proofs.RadenkovicGutmanD1Long30Cells0553
import Proofs.RadenkovicGutmanD1Long30Cells0554
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk110 : List FastNestedCellData.Cell := [leaf01100,leaf01101,leaf01102,leaf01103,leaf01104,leaf01105,leaf01106,leaf01107,leaf01108,leaf01109]
theorem chunk110_checked : chunk110.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk110
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01100_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01101_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01102_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01103_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01104_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01105_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01106_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01107_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01108_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01109_checked
  rfl
#print axioms chunk110_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
