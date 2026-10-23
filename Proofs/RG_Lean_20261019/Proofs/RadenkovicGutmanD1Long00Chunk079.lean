/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0395
import Proofs.RadenkovicGutmanD1Long00Cells0396
import Proofs.RadenkovicGutmanD1Long00Cells0397
import Proofs.RadenkovicGutmanD1Long00Cells0398
import Proofs.RadenkovicGutmanD1Long00Cells0399
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk079 : List FastNestedCellData.Cell := [leaf00790,leaf00791,leaf00792,leaf00793,leaf00794,leaf00795,leaf00796,leaf00797,leaf00798,leaf00799]
theorem chunk079_checked : chunk079.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk079
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00790_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00791_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00792_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00793_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00794_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00795_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00796_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00797_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00798_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00799_checked
  rfl
#print axioms chunk079_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
