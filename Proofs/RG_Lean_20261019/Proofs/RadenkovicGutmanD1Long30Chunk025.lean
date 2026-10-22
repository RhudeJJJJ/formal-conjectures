/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0125
import Proofs.RadenkovicGutmanD1Long30Cells0126
import Proofs.RadenkovicGutmanD1Long30Cells0127
import Proofs.RadenkovicGutmanD1Long30Cells0128
import Proofs.RadenkovicGutmanD1Long30Cells0129
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk025 : List FastNestedCellData.Cell := [leaf00250,leaf00251,leaf00252,leaf00253,leaf00254,leaf00255,leaf00256,leaf00257,leaf00258,leaf00259]
theorem chunk025_checked : chunk025.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk025
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00250_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00251_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00252_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00253_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00254_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00255_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00256_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00257_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00258_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00259_checked
  rfl
#print axioms chunk025_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
