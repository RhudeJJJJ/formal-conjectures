/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0865
import Proofs.RadenkovicGutmanD1Long00Cells0866
import Proofs.RadenkovicGutmanD1Long00Cells0867
import Proofs.RadenkovicGutmanD1Long00Cells0868
import Proofs.RadenkovicGutmanD1Long00Cells0869
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk173 : List FastNestedCellData.Cell := [leaf01730,leaf01731,leaf01732,leaf01733,leaf01734,leaf01735,leaf01736,leaf01737,leaf01738,leaf01739]
theorem chunk173_checked : chunk173.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk173
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01730_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01731_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01732_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01733_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01734_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01735_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01736_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01737_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01738_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01739_checked
  rfl
#print axioms chunk173_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
