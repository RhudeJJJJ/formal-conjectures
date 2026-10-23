/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0810
import Proofs.RadenkovicGutmanD1Long00Cells0811
import Proofs.RadenkovicGutmanD1Long00Cells0812
import Proofs.RadenkovicGutmanD1Long00Cells0813
import Proofs.RadenkovicGutmanD1Long00Cells0814
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk162 : List FastNestedCellData.Cell := [leaf01620,leaf01621,leaf01622,leaf01623,leaf01624,leaf01625,leaf01626,leaf01627,leaf01628,leaf01629]
theorem chunk162_checked : chunk162.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk162
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01620_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01621_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01622_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01623_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01624_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01625_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01626_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01627_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01628_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01629_checked
  rfl
#print axioms chunk162_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
