/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0695
import Proofs.RadenkovicGutmanD1Long00Cells0696
import Proofs.RadenkovicGutmanD1Long00Cells0697
import Proofs.RadenkovicGutmanD1Long00Cells0698
import Proofs.RadenkovicGutmanD1Long00Cells0699
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk139 : List FastNestedCellData.Cell := [leaf01390,leaf01391,leaf01392,leaf01393,leaf01394,leaf01395,leaf01396,leaf01397,leaf01398,leaf01399]
theorem chunk139_checked : chunk139.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk139
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01390_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01391_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01392_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01393_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01394_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01395_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01396_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01397_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01398_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01399_checked
  rfl
#print axioms chunk139_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
