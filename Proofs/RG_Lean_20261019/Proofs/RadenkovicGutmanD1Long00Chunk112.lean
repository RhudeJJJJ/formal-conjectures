/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0560
import Proofs.RadenkovicGutmanD1Long00Cells0561
import Proofs.RadenkovicGutmanD1Long00Cells0562
import Proofs.RadenkovicGutmanD1Long00Cells0563
import Proofs.RadenkovicGutmanD1Long00Cells0564
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk112 : List FastNestedCellData.Cell := [leaf01120,leaf01121,leaf01122,leaf01123,leaf01124,leaf01125,leaf01126,leaf01127,leaf01128,leaf01129]
theorem chunk112_checked : chunk112.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk112
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01120_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01121_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01122_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01123_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01124_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01125_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01126_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01127_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01128_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01129_checked
  rfl
#print axioms chunk112_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
