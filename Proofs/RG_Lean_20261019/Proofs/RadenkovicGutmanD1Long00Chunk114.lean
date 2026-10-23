/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0570
import Proofs.RadenkovicGutmanD1Long00Cells0571
import Proofs.RadenkovicGutmanD1Long00Cells0572
import Proofs.RadenkovicGutmanD1Long00Cells0573
import Proofs.RadenkovicGutmanD1Long00Cells0574
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk114 : List FastNestedCellData.Cell := [leaf01140,leaf01141,leaf01142,leaf01143,leaf01144,leaf01145,leaf01146,leaf01147,leaf01148,leaf01149]
theorem chunk114_checked : chunk114.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk114
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01140_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01141_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01142_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01143_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01144_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01145_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01146_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01147_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01148_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01149_checked
  rfl
#print axioms chunk114_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
