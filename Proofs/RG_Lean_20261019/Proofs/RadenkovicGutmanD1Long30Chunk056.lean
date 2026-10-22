/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0280
import Proofs.RadenkovicGutmanD1Long30Cells0281
import Proofs.RadenkovicGutmanD1Long30Cells0282
import Proofs.RadenkovicGutmanD1Long30Cells0283
import Proofs.RadenkovicGutmanD1Long30Cells0284
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk056 : List FastNestedCellData.Cell := [leaf00560,leaf00561,leaf00562,leaf00563,leaf00564,leaf00565,leaf00566,leaf00567,leaf00568,leaf00569]
theorem chunk056_checked : chunk056.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk056
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00560_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00561_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00562_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00563_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00564_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00565_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00566_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00567_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00568_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00569_checked
  rfl
#print axioms chunk056_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
