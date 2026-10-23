/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0875
import Proofs.RadenkovicGutmanD1Long00Cells0876
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk175 : List FastNestedCellData.Cell := [leaf01750,leaf01751,leaf01752,leaf01753]
theorem chunk175_checked : chunk175.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk175
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01750_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01751_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01752_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01753_checked
  rfl
#print axioms chunk175_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
