/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0400
import Proofs.RadenkovicGutmanD1Long30Cells0401
import Proofs.RadenkovicGutmanD1Long30Cells0402
import Proofs.RadenkovicGutmanD1Long30Cells0403
import Proofs.RadenkovicGutmanD1Long30Cells0404
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk080 : List FastNestedCellData.Cell := [leaf00800,leaf00801,leaf00802,leaf00803,leaf00804,leaf00805,leaf00806,leaf00807,leaf00808,leaf00809]
theorem chunk080_checked : chunk080.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk080
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00800_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00801_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00802_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00803_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00804_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00805_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00806_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00807_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00808_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00809_checked
  rfl
#print axioms chunk080_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
