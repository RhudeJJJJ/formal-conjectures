/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0430
import Proofs.RadenkovicGutmanD1Long30Cells0431
import Proofs.RadenkovicGutmanD1Long30Cells0432
import Proofs.RadenkovicGutmanD1Long30Cells0433
import Proofs.RadenkovicGutmanD1Long30Cells0434
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk086 : List FastNestedCellData.Cell := [leaf00860,leaf00861,leaf00862,leaf00863,leaf00864,leaf00865,leaf00866,leaf00867,leaf00868,leaf00869]
theorem chunk086_checked : chunk086.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk086
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00860_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00861_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00862_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00863_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00864_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00865_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00866_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00867_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00868_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00869_checked
  rfl
#print axioms chunk086_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
