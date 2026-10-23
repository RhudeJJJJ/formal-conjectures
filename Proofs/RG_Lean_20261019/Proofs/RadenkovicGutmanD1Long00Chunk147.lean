/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0735
import Proofs.RadenkovicGutmanD1Long00Cells0736
import Proofs.RadenkovicGutmanD1Long00Cells0737
import Proofs.RadenkovicGutmanD1Long00Cells0738
import Proofs.RadenkovicGutmanD1Long00Cells0739
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk147 : List FastNestedCellData.Cell := [leaf01470,leaf01471,leaf01472,leaf01473,leaf01474,leaf01475,leaf01476,leaf01477,leaf01478,leaf01479]
theorem chunk147_checked : chunk147.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk147
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01470_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01471_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01472_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01473_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01474_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01475_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01476_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01477_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01478_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01479_checked
  rfl
#print axioms chunk147_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
