/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0160
import Proofs.RadenkovicGutmanD1Long00Cells0161
import Proofs.RadenkovicGutmanD1Long00Cells0162
import Proofs.RadenkovicGutmanD1Long00Cells0163
import Proofs.RadenkovicGutmanD1Long00Cells0164
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk032 : List FastNestedCellData.Cell := [leaf00320,leaf00321,leaf00322,leaf00323,leaf00324,leaf00325,leaf00326,leaf00327,leaf00328,leaf00329]
theorem chunk032_checked : chunk032.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk032
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00320_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00321_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00322_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00323_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00324_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00325_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00326_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00327_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00328_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00329_checked
  rfl
#print axioms chunk032_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
