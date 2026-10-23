/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0820
import Proofs.RadenkovicGutmanD1Long00Cells0821
import Proofs.RadenkovicGutmanD1Long00Cells0822
import Proofs.RadenkovicGutmanD1Long00Cells0823
import Proofs.RadenkovicGutmanD1Long00Cells0824
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk164 : List FastNestedCellData.Cell := [leaf01640,leaf01641,leaf01642,leaf01643,leaf01644,leaf01645,leaf01646,leaf01647,leaf01648,leaf01649]
theorem chunk164_checked : chunk164.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk164
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01640_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01641_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01642_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01643_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01644_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01645_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01646_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01647_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01648_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01649_checked
  rfl
#print axioms chunk164_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
