/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0785
import Proofs.RadenkovicGutmanD1Long00Cells0786
import Proofs.RadenkovicGutmanD1Long00Cells0787
import Proofs.RadenkovicGutmanD1Long00Cells0788
import Proofs.RadenkovicGutmanD1Long00Cells0789
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk157 : List FastNestedCellData.Cell := [leaf01570,leaf01571,leaf01572,leaf01573,leaf01574,leaf01575,leaf01576,leaf01577,leaf01578,leaf01579]
theorem chunk157_checked : chunk157.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk157
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01570_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01571_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01572_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01573_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01574_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01575_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01576_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01577_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01578_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01579_checked
  rfl
#print axioms chunk157_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
