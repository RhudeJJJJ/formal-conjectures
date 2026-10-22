/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0145
import Proofs.RadenkovicGutmanD1Long30Cells0146
import Proofs.RadenkovicGutmanD1Long30Cells0147
import Proofs.RadenkovicGutmanD1Long30Cells0148
import Proofs.RadenkovicGutmanD1Long30Cells0149
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk029 : List FastNestedCellData.Cell := [leaf00290,leaf00291,leaf00292,leaf00293,leaf00294,leaf00295,leaf00296,leaf00297,leaf00298,leaf00299]
theorem chunk029_checked : chunk029.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk029
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00290_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00291_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00292_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00293_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00294_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00295_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00296_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00297_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00298_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00299_checked
  rfl
#print axioms chunk029_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
