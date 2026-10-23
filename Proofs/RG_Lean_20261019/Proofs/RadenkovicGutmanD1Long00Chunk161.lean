/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0805
import Proofs.RadenkovicGutmanD1Long00Cells0806
import Proofs.RadenkovicGutmanD1Long00Cells0807
import Proofs.RadenkovicGutmanD1Long00Cells0808
import Proofs.RadenkovicGutmanD1Long00Cells0809
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk161 : List FastNestedCellData.Cell := [leaf01610,leaf01611,leaf01612,leaf01613,leaf01614,leaf01615,leaf01616,leaf01617,leaf01618,leaf01619]
theorem chunk161_checked : chunk161.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk161
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01610_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01611_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01612_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01613_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01614_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01615_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01616_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01617_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01618_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01619_checked
  rfl
#print axioms chunk161_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
