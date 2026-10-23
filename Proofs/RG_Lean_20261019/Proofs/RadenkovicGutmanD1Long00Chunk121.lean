/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0605
import Proofs.RadenkovicGutmanD1Long00Cells0606
import Proofs.RadenkovicGutmanD1Long00Cells0607
import Proofs.RadenkovicGutmanD1Long00Cells0608
import Proofs.RadenkovicGutmanD1Long00Cells0609
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk121 : List FastNestedCellData.Cell := [leaf01210,leaf01211,leaf01212,leaf01213,leaf01214,leaf01215,leaf01216,leaf01217,leaf01218,leaf01219]
theorem chunk121_checked : chunk121.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk121
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01210_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01211_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01212_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01213_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01214_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01215_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01216_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01217_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01218_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01219_checked
  rfl
#print axioms chunk121_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
