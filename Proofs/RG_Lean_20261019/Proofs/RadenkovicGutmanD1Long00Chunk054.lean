/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0270
import Proofs.RadenkovicGutmanD1Long00Cells0271
import Proofs.RadenkovicGutmanD1Long00Cells0272
import Proofs.RadenkovicGutmanD1Long00Cells0273
import Proofs.RadenkovicGutmanD1Long00Cells0274
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk054 : List FastNestedCellData.Cell := [leaf00540,leaf00541,leaf00542,leaf00543,leaf00544,leaf00545,leaf00546,leaf00547,leaf00548,leaf00549]
theorem chunk054_checked : chunk054.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk054
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00540_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00541_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00542_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00543_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00544_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00545_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00546_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00547_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00548_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00549_checked
  rfl
#print axioms chunk054_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
