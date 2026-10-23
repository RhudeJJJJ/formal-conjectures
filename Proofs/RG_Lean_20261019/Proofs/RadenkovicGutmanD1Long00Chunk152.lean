/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0760
import Proofs.RadenkovicGutmanD1Long00Cells0761
import Proofs.RadenkovicGutmanD1Long00Cells0762
import Proofs.RadenkovicGutmanD1Long00Cells0763
import Proofs.RadenkovicGutmanD1Long00Cells0764
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk152 : List FastNestedCellData.Cell := [leaf01520,leaf01521,leaf01522,leaf01523,leaf01524,leaf01525,leaf01526,leaf01527,leaf01528,leaf01529]
theorem chunk152_checked : chunk152.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk152
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01520_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01521_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01522_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01523_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01524_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01525_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01526_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01527_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01528_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01529_checked
  rfl
#print axioms chunk152_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
