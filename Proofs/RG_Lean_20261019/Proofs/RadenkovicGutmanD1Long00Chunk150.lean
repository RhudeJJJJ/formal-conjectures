/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0750
import Proofs.RadenkovicGutmanD1Long00Cells0751
import Proofs.RadenkovicGutmanD1Long00Cells0752
import Proofs.RadenkovicGutmanD1Long00Cells0753
import Proofs.RadenkovicGutmanD1Long00Cells0754
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk150 : List FastNestedCellData.Cell := [leaf01500,leaf01501,leaf01502,leaf01503,leaf01504,leaf01505,leaf01506,leaf01507,leaf01508,leaf01509]
theorem chunk150_checked : chunk150.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk150
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01500_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01501_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01502_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01503_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01504_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01505_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01506_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01507_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01508_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01509_checked
  rfl
#print axioms chunk150_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
