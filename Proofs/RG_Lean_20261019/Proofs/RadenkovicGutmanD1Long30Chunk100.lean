/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0500
import Proofs.RadenkovicGutmanD1Long30Cells0501
import Proofs.RadenkovicGutmanD1Long30Cells0502
import Proofs.RadenkovicGutmanD1Long30Cells0503
import Proofs.RadenkovicGutmanD1Long30Cells0504
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk100 : List FastNestedCellData.Cell := [leaf01000,leaf01001,leaf01002,leaf01003,leaf01004,leaf01005,leaf01006,leaf01007,leaf01008,leaf01009]
theorem chunk100_checked : chunk100.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk100
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01000_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01001_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01002_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01003_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01004_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01005_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01006_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01007_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01008_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01009_checked
  rfl
#print axioms chunk100_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
