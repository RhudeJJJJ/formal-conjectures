/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0200
import Proofs.RadenkovicGutmanD1Long30Cells0201
import Proofs.RadenkovicGutmanD1Long30Cells0202
import Proofs.RadenkovicGutmanD1Long30Cells0203
import Proofs.RadenkovicGutmanD1Long30Cells0204
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk040 : List FastNestedCellData.Cell := [leaf00400,leaf00401,leaf00402,leaf00403,leaf00404,leaf00405,leaf00406,leaf00407,leaf00408,leaf00409]
theorem chunk040_checked : chunk040.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk040
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00400_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00401_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00402_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00403_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00404_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00405_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00406_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00407_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00408_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00409_checked
  rfl
#print axioms chunk040_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
