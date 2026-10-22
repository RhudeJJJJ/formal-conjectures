/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0530
import Proofs.RadenkovicGutmanD1Long30Cells0531
import Proofs.RadenkovicGutmanD1Long30Cells0532
import Proofs.RadenkovicGutmanD1Long30Cells0533
import Proofs.RadenkovicGutmanD1Long30Cells0534
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk106 : List FastNestedCellData.Cell := [leaf01060,leaf01061,leaf01062,leaf01063,leaf01064,leaf01065,leaf01066,leaf01067,leaf01068,leaf01069]
theorem chunk106_checked : chunk106.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk106
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01060_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01061_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01062_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01063_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01064_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01065_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01066_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01067_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01068_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01069_checked
  rfl
#print axioms chunk106_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
