/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0790
import Proofs.RadenkovicGutmanD1Long00Cells0791
import Proofs.RadenkovicGutmanD1Long00Cells0792
import Proofs.RadenkovicGutmanD1Long00Cells0793
import Proofs.RadenkovicGutmanD1Long00Cells0794
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk158 : List FastNestedCellData.Cell := [leaf01580,leaf01581,leaf01582,leaf01583,leaf01584,leaf01585,leaf01586,leaf01587,leaf01588,leaf01589]
theorem chunk158_checked : chunk158.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk158
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01580_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01581_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01582_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01583_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01584_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01585_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01586_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01587_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01588_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01589_checked
  rfl
#print axioms chunk158_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
