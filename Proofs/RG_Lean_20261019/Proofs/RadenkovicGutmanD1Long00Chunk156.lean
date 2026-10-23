/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0780
import Proofs.RadenkovicGutmanD1Long00Cells0781
import Proofs.RadenkovicGutmanD1Long00Cells0782
import Proofs.RadenkovicGutmanD1Long00Cells0783
import Proofs.RadenkovicGutmanD1Long00Cells0784
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk156 : List FastNestedCellData.Cell := [leaf01560,leaf01561,leaf01562,leaf01563,leaf01564,leaf01565,leaf01566,leaf01567,leaf01568,leaf01569]
theorem chunk156_checked : chunk156.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk156
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01560_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01561_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01562_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01563_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01564_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01565_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01566_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01567_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01568_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01569_checked
  rfl
#print axioms chunk156_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
