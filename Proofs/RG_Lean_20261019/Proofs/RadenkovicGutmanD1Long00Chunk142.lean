/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0710
import Proofs.RadenkovicGutmanD1Long00Cells0711
import Proofs.RadenkovicGutmanD1Long00Cells0712
import Proofs.RadenkovicGutmanD1Long00Cells0713
import Proofs.RadenkovicGutmanD1Long00Cells0714
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk142 : List FastNestedCellData.Cell := [leaf01420,leaf01421,leaf01422,leaf01423,leaf01424,leaf01425,leaf01426,leaf01427,leaf01428,leaf01429]
theorem chunk142_checked : chunk142.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk142
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01420_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01421_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01422_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01423_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01424_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01425_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01426_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01427_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01428_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01429_checked
  rfl
#print axioms chunk142_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
