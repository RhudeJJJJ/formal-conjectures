/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0625
import Proofs.RadenkovicGutmanD1Long30Cells0626
import Proofs.RadenkovicGutmanD1Long30Cells0627
import Proofs.RadenkovicGutmanD1Long30Cells0628
import Proofs.RadenkovicGutmanD1Long30Cells0629
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk125 : List FastNestedCellData.Cell := [leaf01250,leaf01251,leaf01252,leaf01253,leaf01254,leaf01255,leaf01256,leaf01257,leaf01258,leaf01259]
theorem chunk125_checked : chunk125.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk125
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01250_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01251_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01252_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01253_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01254_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01255_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01256_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01257_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01258_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01259_checked
  rfl
#print axioms chunk125_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
