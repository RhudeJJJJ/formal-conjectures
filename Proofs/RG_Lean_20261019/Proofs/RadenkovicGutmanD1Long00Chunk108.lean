/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0540
import Proofs.RadenkovicGutmanD1Long00Cells0541
import Proofs.RadenkovicGutmanD1Long00Cells0542
import Proofs.RadenkovicGutmanD1Long00Cells0543
import Proofs.RadenkovicGutmanD1Long00Cells0544
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk108 : List FastNestedCellData.Cell := [leaf01080,leaf01081,leaf01082,leaf01083,leaf01084,leaf01085,leaf01086,leaf01087,leaf01088,leaf01089]
theorem chunk108_checked : chunk108.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk108
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01080_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01081_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01082_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01083_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01084_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01085_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01086_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01087_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01088_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01089_checked
  rfl
#print axioms chunk108_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
