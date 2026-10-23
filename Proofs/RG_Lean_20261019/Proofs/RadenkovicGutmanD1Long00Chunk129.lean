/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0645
import Proofs.RadenkovicGutmanD1Long00Cells0646
import Proofs.RadenkovicGutmanD1Long00Cells0647
import Proofs.RadenkovicGutmanD1Long00Cells0648
import Proofs.RadenkovicGutmanD1Long00Cells0649
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk129 : List FastNestedCellData.Cell := [leaf01290,leaf01291,leaf01292,leaf01293,leaf01294,leaf01295,leaf01296,leaf01297,leaf01298,leaf01299]
theorem chunk129_checked : chunk129.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk129
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01290_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01291_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01292_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01293_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01294_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01295_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01296_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01297_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01298_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01299_checked
  rfl
#print axioms chunk129_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
