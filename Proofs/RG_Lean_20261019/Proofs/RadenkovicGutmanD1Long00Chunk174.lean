/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0870
import Proofs.RadenkovicGutmanD1Long00Cells0871
import Proofs.RadenkovicGutmanD1Long00Cells0872
import Proofs.RadenkovicGutmanD1Long00Cells0873
import Proofs.RadenkovicGutmanD1Long00Cells0874
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk174 : List FastNestedCellData.Cell := [leaf01740,leaf01741,leaf01742,leaf01743,leaf01744,leaf01745,leaf01746,leaf01747,leaf01748,leaf01749]
theorem chunk174_checked : chunk174.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk174
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01740_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01741_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01742_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01743_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01744_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01745_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01746_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01747_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01748_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01749_checked
  rfl
#print axioms chunk174_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
