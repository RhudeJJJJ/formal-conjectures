/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0615
import Proofs.RadenkovicGutmanD1Long30Cells0616
import Proofs.RadenkovicGutmanD1Long30Cells0617
import Proofs.RadenkovicGutmanD1Long30Cells0618
import Proofs.RadenkovicGutmanD1Long30Cells0619
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk123 : List FastNestedCellData.Cell := [leaf01230,leaf01231,leaf01232,leaf01233,leaf01234,leaf01235,leaf01236,leaf01237,leaf01238,leaf01239]
theorem chunk123_checked : chunk123.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk123
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01230_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01231_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01232_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01233_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01234_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01235_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01236_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01237_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01238_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01239_checked
  rfl
#print axioms chunk123_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
