/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0680
import Proofs.RadenkovicGutmanD1Long30Cells0681
import Proofs.RadenkovicGutmanD1Long30Cells0682
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk136 : List FastNestedCellData.Cell := [leaf01360,leaf01361,leaf01362,leaf01363,leaf01364,leaf01365]
theorem chunk136_checked : chunk136.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk136
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01360_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01361_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01362_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01363_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01364_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01365_checked
  rfl
#print axioms chunk136_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
