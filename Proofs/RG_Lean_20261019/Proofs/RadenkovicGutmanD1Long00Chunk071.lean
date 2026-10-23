/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0355
import Proofs.RadenkovicGutmanD1Long00Cells0356
import Proofs.RadenkovicGutmanD1Long00Cells0357
import Proofs.RadenkovicGutmanD1Long00Cells0358
import Proofs.RadenkovicGutmanD1Long00Cells0359
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk071 : List FastNestedCellData.Cell := [leaf00710,leaf00711,leaf00712,leaf00713,leaf00714,leaf00715,leaf00716,leaf00717,leaf00718,leaf00719]
theorem chunk071_checked : chunk071.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk071
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00710_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00711_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00712_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00713_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00714_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00715_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00716_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00717_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00718_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00719_checked
  rfl
#print axioms chunk071_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
