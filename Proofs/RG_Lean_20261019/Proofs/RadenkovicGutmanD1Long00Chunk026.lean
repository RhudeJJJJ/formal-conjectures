/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0130
import Proofs.RadenkovicGutmanD1Long00Cells0131
import Proofs.RadenkovicGutmanD1Long00Cells0132
import Proofs.RadenkovicGutmanD1Long00Cells0133
import Proofs.RadenkovicGutmanD1Long00Cells0134
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk026 : List FastNestedCellData.Cell := [leaf00260,leaf00261,leaf00262,leaf00263,leaf00264,leaf00265,leaf00266,leaf00267,leaf00268,leaf00269]
theorem chunk026_checked : chunk026.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk026
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00260_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00261_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00262_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00263_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00264_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00265_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00266_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00267_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00268_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00269_checked
  rfl
#print axioms chunk026_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
