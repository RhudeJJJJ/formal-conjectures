/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0610
import Proofs.RadenkovicGutmanD1Long00Cells0611
import Proofs.RadenkovicGutmanD1Long00Cells0612
import Proofs.RadenkovicGutmanD1Long00Cells0613
import Proofs.RadenkovicGutmanD1Long00Cells0614
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk122 : List FastNestedCellData.Cell := [leaf01220,leaf01221,leaf01222,leaf01223,leaf01224,leaf01225,leaf01226,leaf01227,leaf01228,leaf01229]
theorem chunk122_checked : chunk122.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk122
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01220_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01221_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01222_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01223_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01224_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01225_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01226_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01227_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01228_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01229_checked
  rfl
#print axioms chunk122_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
