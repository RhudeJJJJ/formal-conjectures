/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0600
import Proofs.RadenkovicGutmanD1Long30Cells0601
import Proofs.RadenkovicGutmanD1Long30Cells0602
import Proofs.RadenkovicGutmanD1Long30Cells0603
import Proofs.RadenkovicGutmanD1Long30Cells0604
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk120 : List FastNestedCellData.Cell := [leaf01200,leaf01201,leaf01202,leaf01203,leaf01204,leaf01205,leaf01206,leaf01207,leaf01208,leaf01209]
theorem chunk120_checked : chunk120.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk120
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01200_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01201_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01202_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01203_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01204_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01205_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01206_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01207_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01208_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01209_checked
  rfl
#print axioms chunk120_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
