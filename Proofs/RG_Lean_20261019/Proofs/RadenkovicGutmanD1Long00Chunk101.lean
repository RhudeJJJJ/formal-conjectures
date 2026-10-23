/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0505
import Proofs.RadenkovicGutmanD1Long00Cells0506
import Proofs.RadenkovicGutmanD1Long00Cells0507
import Proofs.RadenkovicGutmanD1Long00Cells0508
import Proofs.RadenkovicGutmanD1Long00Cells0509
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk101 : List FastNestedCellData.Cell := [leaf01010,leaf01011,leaf01012,leaf01013,leaf01014,leaf01015,leaf01016,leaf01017,leaf01018,leaf01019]
theorem chunk101_checked : chunk101.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk101
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01010_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01011_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01012_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01013_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01014_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01015_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01016_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01017_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01018_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01019_checked
  rfl
#print axioms chunk101_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
