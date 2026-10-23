/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0650
import Proofs.RadenkovicGutmanD1Long00Cells0651
import Proofs.RadenkovicGutmanD1Long00Cells0652
import Proofs.RadenkovicGutmanD1Long00Cells0653
import Proofs.RadenkovicGutmanD1Long00Cells0654
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk130 : List FastNestedCellData.Cell := [leaf01300,leaf01301,leaf01302,leaf01303,leaf01304,leaf01305,leaf01306,leaf01307,leaf01308,leaf01309]
theorem chunk130_checked : chunk130.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk130
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01300_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01301_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01302_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01303_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01304_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01305_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01306_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01307_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01308_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01309_checked
  rfl
#print axioms chunk130_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
