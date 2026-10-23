/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0740
import Proofs.RadenkovicGutmanD1Long00Cells0741
import Proofs.RadenkovicGutmanD1Long00Cells0742
import Proofs.RadenkovicGutmanD1Long00Cells0743
import Proofs.RadenkovicGutmanD1Long00Cells0744
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk148 : List FastNestedCellData.Cell := [leaf01480,leaf01481,leaf01482,leaf01483,leaf01484,leaf01485,leaf01486,leaf01487,leaf01488,leaf01489]
theorem chunk148_checked : chunk148.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk148
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01480_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01481_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01482_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01483_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01484_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01485_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01486_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01487_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01488_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01489_checked
  rfl
#print axioms chunk148_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
