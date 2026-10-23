/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0795
import Proofs.RadenkovicGutmanD1Long00Cells0796
import Proofs.RadenkovicGutmanD1Long00Cells0797
import Proofs.RadenkovicGutmanD1Long00Cells0798
import Proofs.RadenkovicGutmanD1Long00Cells0799
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk159 : List FastNestedCellData.Cell := [leaf01590,leaf01591,leaf01592,leaf01593,leaf01594,leaf01595,leaf01596,leaf01597,leaf01598,leaf01599]
theorem chunk159_checked : chunk159.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk159
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01590_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01591_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01592_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01593_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01594_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01595_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01596_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01597_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01598_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01599_checked
  rfl
#print axioms chunk159_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
