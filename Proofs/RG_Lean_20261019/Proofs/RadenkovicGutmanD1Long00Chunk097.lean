/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0485
import Proofs.RadenkovicGutmanD1Long00Cells0486
import Proofs.RadenkovicGutmanD1Long00Cells0487
import Proofs.RadenkovicGutmanD1Long00Cells0488
import Proofs.RadenkovicGutmanD1Long00Cells0489
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk097 : List FastNestedCellData.Cell := [leaf00970,leaf00971,leaf00972,leaf00973,leaf00974,leaf00975,leaf00976,leaf00977,leaf00978,leaf00979]
theorem chunk097_checked : chunk097.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk097
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00970_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00971_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00972_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00973_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00974_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00975_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00976_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00977_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00978_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00979_checked
  rfl
#print axioms chunk097_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
