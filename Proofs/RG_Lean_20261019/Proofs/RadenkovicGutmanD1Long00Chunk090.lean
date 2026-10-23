/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0450
import Proofs.RadenkovicGutmanD1Long00Cells0451
import Proofs.RadenkovicGutmanD1Long00Cells0452
import Proofs.RadenkovicGutmanD1Long00Cells0453
import Proofs.RadenkovicGutmanD1Long00Cells0454
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk090 : List FastNestedCellData.Cell := [leaf00900,leaf00901,leaf00902,leaf00903,leaf00904,leaf00905,leaf00906,leaf00907,leaf00908,leaf00909]
theorem chunk090_checked : chunk090.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk090
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00900_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00901_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00902_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00903_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00904_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00905_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00906_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00907_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00908_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00909_checked
  rfl
#print axioms chunk090_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
