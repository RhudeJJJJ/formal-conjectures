/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0685
import Proofs.RadenkovicGutmanD1Long00Cells0686
import Proofs.RadenkovicGutmanD1Long00Cells0687
import Proofs.RadenkovicGutmanD1Long00Cells0688
import Proofs.RadenkovicGutmanD1Long00Cells0689
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk137 : List FastNestedCellData.Cell := [leaf01370,leaf01371,leaf01372,leaf01373,leaf01374,leaf01375,leaf01376,leaf01377,leaf01378,leaf01379]
theorem chunk137_checked : chunk137.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk137
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01370_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01371_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01372_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01373_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01374_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01375_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01376_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01377_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01378_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01379_checked
  rfl
#print axioms chunk137_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
