/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0840
import Proofs.RadenkovicGutmanD1Long00Cells0841
import Proofs.RadenkovicGutmanD1Long00Cells0842
import Proofs.RadenkovicGutmanD1Long00Cells0843
import Proofs.RadenkovicGutmanD1Long00Cells0844
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk168 : List FastNestedCellData.Cell := [leaf01680,leaf01681,leaf01682,leaf01683,leaf01684,leaf01685,leaf01686,leaf01687,leaf01688,leaf01689]
theorem chunk168_checked : chunk168.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk168
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01680_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01681_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01682_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01683_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01684_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01685_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01686_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01687_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01688_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01689_checked
  rfl
#print axioms chunk168_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
