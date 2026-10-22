/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0265
import Proofs.RadenkovicGutmanD1Long30Cells0266
import Proofs.RadenkovicGutmanD1Long30Cells0267
import Proofs.RadenkovicGutmanD1Long30Cells0268
import Proofs.RadenkovicGutmanD1Long30Cells0269
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk053 : List FastNestedCellData.Cell := [leaf00530,leaf00531,leaf00532,leaf00533,leaf00534,leaf00535,leaf00536,leaf00537,leaf00538,leaf00539]
theorem chunk053_checked : chunk053.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk053
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00530_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00531_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00532_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00533_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00534_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00535_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00536_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00537_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00538_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00539_checked
  rfl
#print axioms chunk053_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
