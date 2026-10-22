/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0555
import Proofs.RadenkovicGutmanD1Long30Cells0556
import Proofs.RadenkovicGutmanD1Long30Cells0557
import Proofs.RadenkovicGutmanD1Long30Cells0558
import Proofs.RadenkovicGutmanD1Long30Cells0559
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk111 : List FastNestedCellData.Cell := [leaf01110,leaf01111,leaf01112,leaf01113,leaf01114,leaf01115,leaf01116,leaf01117,leaf01118,leaf01119]
theorem chunk111_checked : chunk111.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk111
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01110_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01111_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01112_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01113_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01114_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01115_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01116_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01117_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01118_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01119_checked
  rfl
#print axioms chunk111_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
