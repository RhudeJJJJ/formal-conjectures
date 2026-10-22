/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0010
import Proofs.RadenkovicGutmanD1Long30Cells0011
import Proofs.RadenkovicGutmanD1Long30Cells0012
import Proofs.RadenkovicGutmanD1Long30Cells0013
import Proofs.RadenkovicGutmanD1Long30Cells0014
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk002 : List FastNestedCellData.Cell := [leaf00020,leaf00021,leaf00022,leaf00023,leaf00024,leaf00025,leaf00026,leaf00027,leaf00028,leaf00029]
theorem chunk002_checked : chunk002.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk002
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00020_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00021_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00022_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00023_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00024_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00025_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00026_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00027_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00028_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00029_checked
  rfl
#print axioms chunk002_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
