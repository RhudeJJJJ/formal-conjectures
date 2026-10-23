/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0725
import Proofs.RadenkovicGutmanD1Long00Cells0726
import Proofs.RadenkovicGutmanD1Long00Cells0727
import Proofs.RadenkovicGutmanD1Long00Cells0728
import Proofs.RadenkovicGutmanD1Long00Cells0729
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk145 : List FastNestedCellData.Cell := [leaf01450,leaf01451,leaf01452,leaf01453,leaf01454,leaf01455,leaf01456,leaf01457,leaf01458,leaf01459]
theorem chunk145_checked : chunk145.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk145
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01450_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01451_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01452_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01453_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01454_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01455_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01456_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01457_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01458_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01459_checked
  rfl
#print axioms chunk145_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
