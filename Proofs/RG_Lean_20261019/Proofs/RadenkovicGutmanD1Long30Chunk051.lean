/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0255
import Proofs.RadenkovicGutmanD1Long30Cells0256
import Proofs.RadenkovicGutmanD1Long30Cells0257
import Proofs.RadenkovicGutmanD1Long30Cells0258
import Proofs.RadenkovicGutmanD1Long30Cells0259
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk051 : List FastNestedCellData.Cell := [leaf00510,leaf00511,leaf00512,leaf00513,leaf00514,leaf00515,leaf00516,leaf00517,leaf00518,leaf00519]
theorem chunk051_checked : chunk051.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk051
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00510_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00511_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00512_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00513_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00514_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00515_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00516_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00517_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00518_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00519_checked
  rfl
#print axioms chunk051_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
