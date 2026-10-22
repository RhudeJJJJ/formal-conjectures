/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0635
import Proofs.RadenkovicGutmanD1Long30Cells0636
import Proofs.RadenkovicGutmanD1Long30Cells0637
import Proofs.RadenkovicGutmanD1Long30Cells0638
import Proofs.RadenkovicGutmanD1Long30Cells0639
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk127 : List FastNestedCellData.Cell := [leaf01270,leaf01271,leaf01272,leaf01273,leaf01274,leaf01275,leaf01276,leaf01277,leaf01278,leaf01279]
theorem chunk127_checked : chunk127.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk127
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01270_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01271_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01272_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01273_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01274_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01275_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01276_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01277_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01278_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01279_checked
  rfl
#print axioms chunk127_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
