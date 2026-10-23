/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0185
import Proofs.RadenkovicGutmanD1Long00Cells0186
import Proofs.RadenkovicGutmanD1Long00Cells0187
import Proofs.RadenkovicGutmanD1Long00Cells0188
import Proofs.RadenkovicGutmanD1Long00Cells0189
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk037 : List FastNestedCellData.Cell := [leaf00370,leaf00371,leaf00372,leaf00373,leaf00374,leaf00375,leaf00376,leaf00377,leaf00378,leaf00379]
theorem chunk037_checked : chunk037.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk037
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00370_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00371_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00372_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00373_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00374_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00375_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00376_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00377_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00378_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00379_checked
  rfl
#print axioms chunk037_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
