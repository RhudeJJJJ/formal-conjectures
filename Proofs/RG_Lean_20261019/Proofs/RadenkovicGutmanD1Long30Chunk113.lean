/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0565
import Proofs.RadenkovicGutmanD1Long30Cells0566
import Proofs.RadenkovicGutmanD1Long30Cells0567
import Proofs.RadenkovicGutmanD1Long30Cells0568
import Proofs.RadenkovicGutmanD1Long30Cells0569
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk113 : List FastNestedCellData.Cell := [leaf01130,leaf01131,leaf01132,leaf01133,leaf01134,leaf01135,leaf01136,leaf01137,leaf01138,leaf01139]
theorem chunk113_checked : chunk113.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk113
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01130_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01131_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01132_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01133_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01134_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01135_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01136_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01137_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01138_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01139_checked
  rfl
#print axioms chunk113_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
