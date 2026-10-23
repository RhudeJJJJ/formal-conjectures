/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0850
import Proofs.RadenkovicGutmanD1Long00Cells0851
import Proofs.RadenkovicGutmanD1Long00Cells0852
import Proofs.RadenkovicGutmanD1Long00Cells0853
import Proofs.RadenkovicGutmanD1Long00Cells0854
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk170 : List FastNestedCellData.Cell := [leaf01700,leaf01701,leaf01702,leaf01703,leaf01704,leaf01705,leaf01706,leaf01707,leaf01708,leaf01709]
theorem chunk170_checked : chunk170.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk170
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01700_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01701_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01702_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01703_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01704_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01705_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01706_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01707_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01708_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01709_checked
  rfl
#print axioms chunk170_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
