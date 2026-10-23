/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0105
import Proofs.RadenkovicGutmanD1Long00Cells0106
import Proofs.RadenkovicGutmanD1Long00Cells0107
import Proofs.RadenkovicGutmanD1Long00Cells0108
import Proofs.RadenkovicGutmanD1Long00Cells0109
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk021 : List FastNestedCellData.Cell := [leaf00210,leaf00211,leaf00212,leaf00213,leaf00214,leaf00215,leaf00216,leaf00217,leaf00218,leaf00219]
theorem chunk021_checked : chunk021.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk021
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00210_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00211_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00212_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00213_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00214_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00215_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00216_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00217_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00218_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00219_checked
  rfl
#print axioms chunk021_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
