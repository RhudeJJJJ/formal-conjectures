/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0670
import Proofs.RadenkovicGutmanD1Long30Cells0671
import Proofs.RadenkovicGutmanD1Long30Cells0672
import Proofs.RadenkovicGutmanD1Long30Cells0673
import Proofs.RadenkovicGutmanD1Long30Cells0674
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk134 : List FastNestedCellData.Cell := [leaf01340,leaf01341,leaf01342,leaf01343,leaf01344,leaf01345,leaf01346,leaf01347,leaf01348,leaf01349]
theorem chunk134_checked : chunk134.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk134
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01340_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01341_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01342_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01343_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01344_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01345_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01346_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01347_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01348_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01349_checked
  rfl
#print axioms chunk134_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
