/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0745
import Proofs.RadenkovicGutmanD1Long00Cells0746
import Proofs.RadenkovicGutmanD1Long00Cells0747
import Proofs.RadenkovicGutmanD1Long00Cells0748
import Proofs.RadenkovicGutmanD1Long00Cells0749
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk149 : List FastNestedCellData.Cell := [leaf01490,leaf01491,leaf01492,leaf01493,leaf01494,leaf01495,leaf01496,leaf01497,leaf01498,leaf01499]
theorem chunk149_checked : chunk149.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk149
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01490_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01491_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01492_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01493_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01494_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01495_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01496_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01497_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01498_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01499_checked
  rfl
#print axioms chunk149_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
