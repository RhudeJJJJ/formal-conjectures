/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long10Cells0110
import Proofs.RadenkovicGutmanD1Long10Cells0111
import Proofs.RadenkovicGutmanD1Long10Cells0112
import Proofs.RadenkovicGutmanD1Long10Cells0113
import Proofs.RadenkovicGutmanD1Long10Cells0114
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
def chunk022 : List FastNestedCellData.Cell := [leaf00220,leaf00221,leaf00222,leaf00223,leaf00224,leaf00225,leaf00226,leaf00227,leaf00228,leaf00229]
theorem chunk022_checked : chunk022.all (FastNestedCellData.accepts 1 0 4)=true := by
  unfold chunk022
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00220_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00221_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00222_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00223_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00224_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00225_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00226_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00227_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00228_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00229_checked
  rfl
#print axioms chunk022_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
