/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0835
import Proofs.RadenkovicGutmanD1Long00Cells0836
import Proofs.RadenkovicGutmanD1Long00Cells0837
import Proofs.RadenkovicGutmanD1Long00Cells0838
import Proofs.RadenkovicGutmanD1Long00Cells0839
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk167 : List FastNestedCellData.Cell := [leaf01670,leaf01671,leaf01672,leaf01673,leaf01674,leaf01675,leaf01676,leaf01677,leaf01678,leaf01679]
theorem chunk167_checked : chunk167.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk167
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01670_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01671_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01672_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01673_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01674_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01675_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01676_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01677_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01678_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01679_checked
  rfl
#print axioms chunk167_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
