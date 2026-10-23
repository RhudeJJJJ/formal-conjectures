/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0815
import Proofs.RadenkovicGutmanD1Long00Cells0816
import Proofs.RadenkovicGutmanD1Long00Cells0817
import Proofs.RadenkovicGutmanD1Long00Cells0818
import Proofs.RadenkovicGutmanD1Long00Cells0819
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk163 : List FastNestedCellData.Cell := [leaf01630,leaf01631,leaf01632,leaf01633,leaf01634,leaf01635,leaf01636,leaf01637,leaf01638,leaf01639]
theorem chunk163_checked : chunk163.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk163
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01630_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01631_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01632_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01633_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01634_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01635_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01636_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01637_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01638_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01639_checked
  rfl
#print axioms chunk163_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
