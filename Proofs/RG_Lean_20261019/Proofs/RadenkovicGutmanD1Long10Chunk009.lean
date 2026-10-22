/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0045
import Proofs.RadenkovicGutmanD1Long10Cells0046
import Proofs.RadenkovicGutmanD1Long10Cells0047
import Proofs.RadenkovicGutmanD1Long10Cells0048
import Proofs.RadenkovicGutmanD1Long10Cells0049
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk009 : List FastNestedCellData.Cell := [leaf00090,leaf00091,leaf00092,leaf00093,leaf00094,leaf00095,leaf00096,leaf00097,leaf00098,leaf00099]
theorem chunk009_checked : chunk009.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk009
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00090_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00091_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00092_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00093_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00094_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00095_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00096_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00097_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00098_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00099_checked
  rfl
#print axioms chunk009_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
