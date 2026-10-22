/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0240
import Proofs.RadenkovicGutmanD1Long30Cells0241
import Proofs.RadenkovicGutmanD1Long30Cells0242
import Proofs.RadenkovicGutmanD1Long30Cells0243
import Proofs.RadenkovicGutmanD1Long30Cells0244
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk048 : List FastNestedCellData.Cell := [leaf00480,leaf00481,leaf00482,leaf00483,leaf00484,leaf00485,leaf00486,leaf00487,leaf00488,leaf00489]
theorem chunk048_checked : chunk048.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk048
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00480_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00481_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00482_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00483_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00484_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00485_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00486_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00487_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00488_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00489_checked
  rfl
#print axioms chunk048_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
