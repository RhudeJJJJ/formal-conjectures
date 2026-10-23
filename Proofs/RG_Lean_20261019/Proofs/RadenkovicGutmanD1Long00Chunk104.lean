/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0520
import Proofs.RadenkovicGutmanD1Long00Cells0521
import Proofs.RadenkovicGutmanD1Long00Cells0522
import Proofs.RadenkovicGutmanD1Long00Cells0523
import Proofs.RadenkovicGutmanD1Long00Cells0524
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk104 : List FastNestedCellData.Cell := [leaf01040,leaf01041,leaf01042,leaf01043,leaf01044,leaf01045,leaf01046,leaf01047,leaf01048,leaf01049]
theorem chunk104_checked : chunk104.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk104
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01040_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01041_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01042_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01043_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01044_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01045_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01046_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01047_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01048_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01049_checked
  rfl
#print axioms chunk104_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
