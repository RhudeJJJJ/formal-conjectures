/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0845
import Proofs.RadenkovicGutmanD1Long00Cells0846
import Proofs.RadenkovicGutmanD1Long00Cells0847
import Proofs.RadenkovicGutmanD1Long00Cells0848
import Proofs.RadenkovicGutmanD1Long00Cells0849
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk169 : List FastNestedCellData.Cell := [leaf01690,leaf01691,leaf01692,leaf01693,leaf01694,leaf01695,leaf01696,leaf01697,leaf01698,leaf01699]
theorem chunk169_checked : chunk169.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk169
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01690_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01691_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01692_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01693_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01694_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01695_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01696_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01697_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01698_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01699_checked
  rfl
#print axioms chunk169_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
