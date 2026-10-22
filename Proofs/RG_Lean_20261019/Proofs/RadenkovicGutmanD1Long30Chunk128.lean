/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0640
import Proofs.RadenkovicGutmanD1Long30Cells0641
import Proofs.RadenkovicGutmanD1Long30Cells0642
import Proofs.RadenkovicGutmanD1Long30Cells0643
import Proofs.RadenkovicGutmanD1Long30Cells0644
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk128 : List FastNestedCellData.Cell := [leaf01280,leaf01281,leaf01282,leaf01283,leaf01284,leaf01285,leaf01286,leaf01287,leaf01288,leaf01289]
theorem chunk128_checked : chunk128.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk128
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01280_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01281_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01282_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01283_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01284_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01285_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01286_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01287_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01288_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01289_checked
  rfl
#print axioms chunk128_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
