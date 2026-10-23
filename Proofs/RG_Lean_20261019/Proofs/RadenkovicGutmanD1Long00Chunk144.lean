/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0720
import Proofs.RadenkovicGutmanD1Long00Cells0721
import Proofs.RadenkovicGutmanD1Long00Cells0722
import Proofs.RadenkovicGutmanD1Long00Cells0723
import Proofs.RadenkovicGutmanD1Long00Cells0724
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk144 : List FastNestedCellData.Cell := [leaf01440,leaf01441,leaf01442,leaf01443,leaf01444,leaf01445,leaf01446,leaf01447,leaf01448,leaf01449]
theorem chunk144_checked : chunk144.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk144
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01440_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01441_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01442_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01443_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01444_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01445_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01446_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01447_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01448_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01449_checked
  rfl
#print axioms chunk144_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
