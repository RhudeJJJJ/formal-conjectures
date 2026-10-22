/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0115
import Proofs.RadenkovicGutmanD1Long30Cells0116
import Proofs.RadenkovicGutmanD1Long30Cells0117
import Proofs.RadenkovicGutmanD1Long30Cells0118
import Proofs.RadenkovicGutmanD1Long30Cells0119
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk023 : List FastNestedCellData.Cell := [leaf00230,leaf00231,leaf00232,leaf00233,leaf00234,leaf00235,leaf00236,leaf00237,leaf00238,leaf00239]
theorem chunk023_checked : chunk023.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk023
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00230_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00231_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00232_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00233_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00234_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00235_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00236_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00237_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00238_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00239_checked
  rfl
#print axioms chunk023_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
