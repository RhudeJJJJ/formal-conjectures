/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0825
import Proofs.RadenkovicGutmanD1Long00Cells0826
import Proofs.RadenkovicGutmanD1Long00Cells0827
import Proofs.RadenkovicGutmanD1Long00Cells0828
import Proofs.RadenkovicGutmanD1Long00Cells0829
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk165 : List FastNestedCellData.Cell := [leaf01650,leaf01651,leaf01652,leaf01653,leaf01654,leaf01655,leaf01656,leaf01657,leaf01658,leaf01659]
theorem chunk165_checked : chunk165.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk165
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01650_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01651_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01652_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01653_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01654_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01655_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01656_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01657_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01658_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01659_checked
  rfl
#print axioms chunk165_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
