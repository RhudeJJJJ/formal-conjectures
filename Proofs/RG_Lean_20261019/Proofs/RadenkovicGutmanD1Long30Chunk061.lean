/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0305
import Proofs.RadenkovicGutmanD1Long30Cells0306
import Proofs.RadenkovicGutmanD1Long30Cells0307
import Proofs.RadenkovicGutmanD1Long30Cells0308
import Proofs.RadenkovicGutmanD1Long30Cells0309
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk061 : List FastNestedCellData.Cell := [leaf00610,leaf00611,leaf00612,leaf00613,leaf00614,leaf00615,leaf00616,leaf00617,leaf00618,leaf00619]
theorem chunk061_checked : chunk061.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk061
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00610_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00611_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00612_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00613_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00614_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00615_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00616_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00617_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00618_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00619_checked
  rfl
#print axioms chunk061_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
