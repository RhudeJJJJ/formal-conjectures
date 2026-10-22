/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0675
import Proofs.RadenkovicGutmanD1Long30Cells0676
import Proofs.RadenkovicGutmanD1Long30Cells0677
import Proofs.RadenkovicGutmanD1Long30Cells0678
import Proofs.RadenkovicGutmanD1Long30Cells0679
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk135 : List FastNestedCellData.Cell := [leaf01350,leaf01351,leaf01352,leaf01353,leaf01354,leaf01355,leaf01356,leaf01357,leaf01358,leaf01359]
theorem chunk135_checked : chunk135.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk135
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01350_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01351_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01352_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01353_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01354_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01355_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01356_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01357_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01358_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01359_checked
  rfl
#print axioms chunk135_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
