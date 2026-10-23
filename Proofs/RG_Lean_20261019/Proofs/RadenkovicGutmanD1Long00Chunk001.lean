/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0005
import Proofs.RadenkovicGutmanD1Long00Cells0006
import Proofs.RadenkovicGutmanD1Long00Cells0007
import Proofs.RadenkovicGutmanD1Long00Cells0008
import Proofs.RadenkovicGutmanD1Long00Cells0009
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk001 : List FastNestedCellData.Cell := [leaf00010,leaf00011,leaf00012,leaf00013,leaf00014,leaf00015,leaf00016,leaf00017,leaf00018,leaf00019]
theorem chunk001_checked : chunk001.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk001
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00010_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00011_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00012_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00013_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00014_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00015_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00016_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00017_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00018_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00019_checked
  rfl
#print axioms chunk001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
