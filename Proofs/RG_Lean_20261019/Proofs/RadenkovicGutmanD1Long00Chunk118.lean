/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0590
import Proofs.RadenkovicGutmanD1Long00Cells0591
import Proofs.RadenkovicGutmanD1Long00Cells0592
import Proofs.RadenkovicGutmanD1Long00Cells0593
import Proofs.RadenkovicGutmanD1Long00Cells0594
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk118 : List FastNestedCellData.Cell := [leaf01180,leaf01181,leaf01182,leaf01183,leaf01184,leaf01185,leaf01186,leaf01187,leaf01188,leaf01189]
theorem chunk118_checked : chunk118.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk118
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01180_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01181_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01182_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01183_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01184_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01185_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01186_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01187_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01188_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01189_checked
  rfl
#print axioms chunk118_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
