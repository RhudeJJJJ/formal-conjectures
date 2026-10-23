/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0770
import Proofs.RadenkovicGutmanD1Long00Cells0771
import Proofs.RadenkovicGutmanD1Long00Cells0772
import Proofs.RadenkovicGutmanD1Long00Cells0773
import Proofs.RadenkovicGutmanD1Long00Cells0774
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk154 : List FastNestedCellData.Cell := [leaf01540,leaf01541,leaf01542,leaf01543,leaf01544,leaf01545,leaf01546,leaf01547,leaf01548,leaf01549]
theorem chunk154_checked : chunk154.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk154
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01540_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01541_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01542_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01543_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01544_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01545_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01546_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01547_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01548_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01549_checked
  rfl
#print axioms chunk154_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
