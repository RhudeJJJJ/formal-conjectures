/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0700
import Proofs.RadenkovicGutmanD1Long00Cells0701
import Proofs.RadenkovicGutmanD1Long00Cells0702
import Proofs.RadenkovicGutmanD1Long00Cells0703
import Proofs.RadenkovicGutmanD1Long00Cells0704
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk140 : List FastNestedCellData.Cell := [leaf01400,leaf01401,leaf01402,leaf01403,leaf01404,leaf01405,leaf01406,leaf01407,leaf01408,leaf01409]
theorem chunk140_checked : chunk140.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk140
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01400_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01401_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01402_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01403_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01404_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01405_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01406_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01407_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01408_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01409_checked
  rfl
#print axioms chunk140_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
