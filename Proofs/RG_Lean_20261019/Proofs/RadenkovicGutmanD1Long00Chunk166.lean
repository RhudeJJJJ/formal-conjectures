/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0830
import Proofs.RadenkovicGutmanD1Long00Cells0831
import Proofs.RadenkovicGutmanD1Long00Cells0832
import Proofs.RadenkovicGutmanD1Long00Cells0833
import Proofs.RadenkovicGutmanD1Long00Cells0834
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk166 : List FastNestedCellData.Cell := [leaf01660,leaf01661,leaf01662,leaf01663,leaf01664,leaf01665,leaf01666,leaf01667,leaf01668,leaf01669]
theorem chunk166_checked : chunk166.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk166
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01660_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01661_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01662_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01663_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01664_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01665_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01666_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01667_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01668_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01669_checked
  rfl
#print axioms chunk166_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
