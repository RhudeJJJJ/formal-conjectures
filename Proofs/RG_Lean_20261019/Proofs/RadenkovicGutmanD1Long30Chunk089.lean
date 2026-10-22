/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0445
import Proofs.RadenkovicGutmanD1Long30Cells0446
import Proofs.RadenkovicGutmanD1Long30Cells0447
import Proofs.RadenkovicGutmanD1Long30Cells0448
import Proofs.RadenkovicGutmanD1Long30Cells0449
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk089 : List FastNestedCellData.Cell := [leaf00890,leaf00891,leaf00892,leaf00893,leaf00894,leaf00895,leaf00896,leaf00897,leaf00898,leaf00899]
theorem chunk089_checked : chunk089.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk089
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00890_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00891_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00892_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00893_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00894_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00895_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00896_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00897_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00898_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00899_checked
  rfl
#print axioms chunk089_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
