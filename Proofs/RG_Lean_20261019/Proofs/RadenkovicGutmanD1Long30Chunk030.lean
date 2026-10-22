/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0150
import Proofs.RadenkovicGutmanD1Long30Cells0151
import Proofs.RadenkovicGutmanD1Long30Cells0152
import Proofs.RadenkovicGutmanD1Long30Cells0153
import Proofs.RadenkovicGutmanD1Long30Cells0154
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk030 : List FastNestedCellData.Cell := [leaf00300,leaf00301,leaf00302,leaf00303,leaf00304,leaf00305,leaf00306,leaf00307,leaf00308,leaf00309]
theorem chunk030_checked : chunk030.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk030
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00300_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00301_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00302_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00303_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00304_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00305_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00306_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00307_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00308_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00309_checked
  rfl
#print axioms chunk030_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
