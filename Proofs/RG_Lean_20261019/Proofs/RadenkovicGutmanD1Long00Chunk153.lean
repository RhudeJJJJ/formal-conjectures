/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0765
import Proofs.RadenkovicGutmanD1Long00Cells0766
import Proofs.RadenkovicGutmanD1Long00Cells0767
import Proofs.RadenkovicGutmanD1Long00Cells0768
import Proofs.RadenkovicGutmanD1Long00Cells0769
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk153 : List FastNestedCellData.Cell := [leaf01530,leaf01531,leaf01532,leaf01533,leaf01534,leaf01535,leaf01536,leaf01537,leaf01538,leaf01539]
theorem chunk153_checked : chunk153.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk153
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01530_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01531_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01532_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01533_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01534_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01535_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01536_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01537_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01538_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01539_checked
  rfl
#print axioms chunk153_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
