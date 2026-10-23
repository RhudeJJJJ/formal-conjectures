/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0730
import Proofs.RadenkovicGutmanD1Long00Cells0731
import Proofs.RadenkovicGutmanD1Long00Cells0732
import Proofs.RadenkovicGutmanD1Long00Cells0733
import Proofs.RadenkovicGutmanD1Long00Cells0734
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk146 : List FastNestedCellData.Cell := [leaf01460,leaf01461,leaf01462,leaf01463,leaf01464,leaf01465,leaf01466,leaf01467,leaf01468,leaf01469]
theorem chunk146_checked : chunk146.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk146
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01460_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01461_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01462_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01463_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01464_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01465_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01466_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01467_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01468_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01469_checked
  rfl
#print axioms chunk146_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
