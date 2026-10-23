/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0180
import Proofs.RadenkovicGutmanD1Long00Cells0181
import Proofs.RadenkovicGutmanD1Long00Cells0182
import Proofs.RadenkovicGutmanD1Long00Cells0183
import Proofs.RadenkovicGutmanD1Long00Cells0184
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk036 : List FastNestedCellData.Cell := [leaf00360,leaf00361,leaf00362,leaf00363,leaf00364,leaf00365,leaf00366,leaf00367,leaf00368,leaf00369]
theorem chunk036_checked : chunk036.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk036
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00360_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00361_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00362_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00363_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00364_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00365_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00366_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00367_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00368_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00369_checked
  rfl
#print axioms chunk036_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
