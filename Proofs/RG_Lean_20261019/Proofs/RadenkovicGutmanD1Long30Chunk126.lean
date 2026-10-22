/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0630
import Proofs.RadenkovicGutmanD1Long30Cells0631
import Proofs.RadenkovicGutmanD1Long30Cells0632
import Proofs.RadenkovicGutmanD1Long30Cells0633
import Proofs.RadenkovicGutmanD1Long30Cells0634
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk126 : List FastNestedCellData.Cell := [leaf01260,leaf01261,leaf01262,leaf01263,leaf01264,leaf01265,leaf01266,leaf01267,leaf01268,leaf01269]
theorem chunk126_checked : chunk126.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk126
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01260_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01261_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01262_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01263_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01264_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01265_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01266_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01267_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01268_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01269_checked
  rfl
#print axioms chunk126_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
