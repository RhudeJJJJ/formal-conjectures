/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0190
import Proofs.RadenkovicGutmanD1Long30Cells0191
import Proofs.RadenkovicGutmanD1Long30Cells0192
import Proofs.RadenkovicGutmanD1Long30Cells0193
import Proofs.RadenkovicGutmanD1Long30Cells0194
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk038 : List FastNestedCellData.Cell := [leaf00380,leaf00381,leaf00382,leaf00383,leaf00384,leaf00385,leaf00386,leaf00387,leaf00388,leaf00389]
theorem chunk038_checked : chunk038.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk038
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00380_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00381_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00382_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00383_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00384_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00385_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00386_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00387_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00388_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00389_checked
  rfl
#print axioms chunk038_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
