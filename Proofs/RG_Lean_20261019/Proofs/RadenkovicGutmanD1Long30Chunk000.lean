/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long30Cells0000
import Proofs.RadenkovicGutmanD1Long30Cells0001
import Proofs.RadenkovicGutmanD1Long30Cells0002
import Proofs.RadenkovicGutmanD1Long30Cells0003
import Proofs.RadenkovicGutmanD1Long30Cells0004
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
def chunk000 : List FastNestedCellData.Cell := [leaf00000,leaf00001,leaf00002,leaf00003,leaf00004,leaf00005,leaf00006,leaf00007,leaf00008,leaf00009]
theorem chunk000_checked : chunk000.all (FastNestedCellData.accepts 1 2 4)=true := by
  unfold chunk000
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00000_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00001_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00002_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00003_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00004_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00005_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00006_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00007_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00008_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf00009_checked
  rfl
#print axioms chunk000_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
