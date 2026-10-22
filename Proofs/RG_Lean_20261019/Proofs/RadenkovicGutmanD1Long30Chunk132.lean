/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0660
import Proofs.RadenkovicGutmanD1Long30Cells0661
import Proofs.RadenkovicGutmanD1Long30Cells0662
import Proofs.RadenkovicGutmanD1Long30Cells0663
import Proofs.RadenkovicGutmanD1Long30Cells0664
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk132 : List FastNestedCellData.Cell := [leaf01320,leaf01321,leaf01322,leaf01323,leaf01324,leaf01325,leaf01326,leaf01327,leaf01328,leaf01329]
theorem chunk132_checked : chunk132.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk132
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01320_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01321_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01322_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01323_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01324_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01325_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01326_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01327_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01328_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01329_checked
  rfl
#print axioms chunk132_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
