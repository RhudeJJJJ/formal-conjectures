/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0040
import Proofs.RadenkovicGutmanD1Long30Cells0041
import Proofs.RadenkovicGutmanD1Long30Cells0042
import Proofs.RadenkovicGutmanD1Long30Cells0043
import Proofs.RadenkovicGutmanD1Long30Cells0044
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk008 : List FastNestedCellData.Cell := [leaf00080,leaf00081,leaf00082,leaf00083,leaf00084,leaf00085,leaf00086,leaf00087,leaf00088,leaf00089]
theorem chunk008_checked : chunk008.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk008
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00080_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00081_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00082_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00083_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00084_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00085_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00086_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00087_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00088_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00089_checked
  rfl
#print axioms chunk008_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
