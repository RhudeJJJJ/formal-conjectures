/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0320
import Proofs.RadenkovicGutmanD1Long00Cells0321
import Proofs.RadenkovicGutmanD1Long00Cells0322
import Proofs.RadenkovicGutmanD1Long00Cells0323
import Proofs.RadenkovicGutmanD1Long00Cells0324
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk064 : List FastNestedCellData.Cell := [leaf00640,leaf00641,leaf00642,leaf00643,leaf00644,leaf00645,leaf00646,leaf00647,leaf00648,leaf00649]
theorem chunk064_checked : chunk064.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk064
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00640_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00641_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00642_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00643_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00644_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00645_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00646_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00647_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00648_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00649_checked
  rfl
#print axioms chunk064_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
