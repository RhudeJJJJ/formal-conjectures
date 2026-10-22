/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0385
import Proofs.RadenkovicGutmanD1Long30Cells0386
import Proofs.RadenkovicGutmanD1Long30Cells0387
import Proofs.RadenkovicGutmanD1Long30Cells0388
import Proofs.RadenkovicGutmanD1Long30Cells0389
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk077 : List FastNestedCellData.Cell := [leaf00770,leaf00771,leaf00772,leaf00773,leaf00774,leaf00775,leaf00776,leaf00777,leaf00778,leaf00779]
theorem chunk077_checked : chunk077.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk077
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00770_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00771_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00772_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00773_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00774_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00775_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00776_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00777_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00778_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00779_checked
  rfl
#print axioms chunk077_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
