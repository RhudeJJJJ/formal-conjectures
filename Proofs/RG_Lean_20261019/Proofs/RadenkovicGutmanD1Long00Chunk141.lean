/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0705
import Proofs.RadenkovicGutmanD1Long00Cells0706
import Proofs.RadenkovicGutmanD1Long00Cells0707
import Proofs.RadenkovicGutmanD1Long00Cells0708
import Proofs.RadenkovicGutmanD1Long00Cells0709
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk141 : List FastNestedCellData.Cell := [leaf01410,leaf01411,leaf01412,leaf01413,leaf01414,leaf01415,leaf01416,leaf01417,leaf01418,leaf01419]
theorem chunk141_checked : chunk141.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk141
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01410_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01411_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01412_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01413_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01414_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01415_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01416_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01417_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01418_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01419_checked
  rfl
#print axioms chunk141_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
