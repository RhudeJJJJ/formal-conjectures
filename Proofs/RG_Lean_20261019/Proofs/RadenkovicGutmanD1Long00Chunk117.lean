/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0585
import Proofs.RadenkovicGutmanD1Long00Cells0586
import Proofs.RadenkovicGutmanD1Long00Cells0587
import Proofs.RadenkovicGutmanD1Long00Cells0588
import Proofs.RadenkovicGutmanD1Long00Cells0589
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk117 : List FastNestedCellData.Cell := [leaf01170,leaf01171,leaf01172,leaf01173,leaf01174,leaf01175,leaf01176,leaf01177,leaf01178,leaf01179]
theorem chunk117_checked : chunk117.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk117
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01170_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01171_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01172_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01173_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01174_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01175_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01176_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01177_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01178_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01179_checked
  rfl
#print axioms chunk117_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
