/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0860
import Proofs.RadenkovicGutmanD1Long00Cells0861
import Proofs.RadenkovicGutmanD1Long00Cells0862
import Proofs.RadenkovicGutmanD1Long00Cells0863
import Proofs.RadenkovicGutmanD1Long00Cells0864
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk172 : List FastNestedCellData.Cell := [leaf01720,leaf01721,leaf01722,leaf01723,leaf01724,leaf01725,leaf01726,leaf01727,leaf01728,leaf01729]
theorem chunk172_checked : chunk172.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk172
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01720_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01721_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01722_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01723_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01724_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01725_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01726_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01727_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01728_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01729_checked
  rfl
#print axioms chunk172_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
