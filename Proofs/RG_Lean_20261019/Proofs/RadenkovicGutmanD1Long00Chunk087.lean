/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0435
import Proofs.RadenkovicGutmanD1Long00Cells0436
import Proofs.RadenkovicGutmanD1Long00Cells0437
import Proofs.RadenkovicGutmanD1Long00Cells0438
import Proofs.RadenkovicGutmanD1Long00Cells0439
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk087 : List FastNestedCellData.Cell := [leaf00870,leaf00871,leaf00872,leaf00873,leaf00874,leaf00875,leaf00876,leaf00877,leaf00878,leaf00879]
theorem chunk087_checked : chunk087.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk087
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00870_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00871_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00872_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00873_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00874_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00875_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00876_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00877_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00878_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00879_checked
  rfl
#print axioms chunk087_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
