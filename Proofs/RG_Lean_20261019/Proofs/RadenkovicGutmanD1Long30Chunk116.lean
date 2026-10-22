/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0580
import Proofs.RadenkovicGutmanD1Long30Cells0581
import Proofs.RadenkovicGutmanD1Long30Cells0582
import Proofs.RadenkovicGutmanD1Long30Cells0583
import Proofs.RadenkovicGutmanD1Long30Cells0584
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk116 : List FastNestedCellData.Cell := [leaf01160,leaf01161,leaf01162,leaf01163,leaf01164,leaf01165,leaf01166,leaf01167,leaf01168,leaf01169]
theorem chunk116_checked : chunk116.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk116
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01160_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01161_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01162_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01163_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01164_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01165_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01166_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01167_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01168_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01169_checked
  rfl
#print axioms chunk116_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
