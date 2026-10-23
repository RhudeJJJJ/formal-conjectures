/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0755
import Proofs.RadenkovicGutmanD1Long00Cells0756
import Proofs.RadenkovicGutmanD1Long00Cells0757
import Proofs.RadenkovicGutmanD1Long00Cells0758
import Proofs.RadenkovicGutmanD1Long00Cells0759
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk151 : List FastNestedCellData.Cell := [leaf01510,leaf01511,leaf01512,leaf01513,leaf01514,leaf01515,leaf01516,leaf01517,leaf01518,leaf01519]
theorem chunk151_checked : chunk151.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk151
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01510_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01511_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01512_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01513_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01514_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01515_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01516_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01517_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01518_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01519_checked
  rfl
#print axioms chunk151_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
