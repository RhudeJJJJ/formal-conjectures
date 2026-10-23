/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0800
import Proofs.RadenkovicGutmanD1Long00Cells0801
import Proofs.RadenkovicGutmanD1Long00Cells0802
import Proofs.RadenkovicGutmanD1Long00Cells0803
import Proofs.RadenkovicGutmanD1Long00Cells0804
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk160 : List FastNestedCellData.Cell := [leaf01600,leaf01601,leaf01602,leaf01603,leaf01604,leaf01605,leaf01606,leaf01607,leaf01608,leaf01609]
theorem chunk160_checked : chunk160.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk160
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01600_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01601_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01602_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01603_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01604_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01605_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01606_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01607_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01608_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01609_checked
  rfl
#print axioms chunk160_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
