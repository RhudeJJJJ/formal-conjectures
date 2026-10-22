/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0075
import Proofs.RadenkovicGutmanD1Long30Cells0076
import Proofs.RadenkovicGutmanD1Long30Cells0077
import Proofs.RadenkovicGutmanD1Long30Cells0078
import Proofs.RadenkovicGutmanD1Long30Cells0079
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk015 : List FastNestedCellData.Cell := [leaf00150,leaf00151,leaf00152,leaf00153,leaf00154,leaf00155,leaf00156,leaf00157,leaf00158,leaf00159]
theorem chunk015_checked : chunk015.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk015
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00150_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00151_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00152_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00153_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00154_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00155_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00156_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00157_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00158_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00159_checked
  rfl
#print axioms chunk015_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
