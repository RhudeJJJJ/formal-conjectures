/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0050
import Proofs.RadenkovicGutmanD1Long30Cells0051
import Proofs.RadenkovicGutmanD1Long30Cells0052
import Proofs.RadenkovicGutmanD1Long30Cells0053
import Proofs.RadenkovicGutmanD1Long30Cells0054
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk010 : List FastNestedCellData.Cell := [leaf00100,leaf00101,leaf00102,leaf00103,leaf00104,leaf00105,leaf00106,leaf00107,leaf00108,leaf00109]
theorem chunk010_checked : chunk010.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk010
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00100_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00101_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00102_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00103_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00104_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00105_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00106_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00107_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00108_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00109_checked
  rfl
#print axioms chunk010_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
