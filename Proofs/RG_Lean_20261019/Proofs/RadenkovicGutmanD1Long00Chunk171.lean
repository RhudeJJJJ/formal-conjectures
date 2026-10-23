/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmCoverChecks
import Proofs.RadenkovicGutmanD1Long00Cells0855
import Proofs.RadenkovicGutmanD1Long00Cells0856
import Proofs.RadenkovicGutmanD1Long00Cells0857
import Proofs.RadenkovicGutmanD1Long00Cells0858
import Proofs.RadenkovicGutmanD1Long00Cells0859
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
def chunk171 : List FastNestedCellData.Cell := [leaf01710,leaf01711,leaf01712,leaf01713,leaf01714,leaf01715,leaf01716,leaf01717,leaf01718,leaf01719]
theorem chunk171_checked : chunk171.all (FastNestedCellData.accepts 1 4 4)=true := by
  unfold chunk171
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01710_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01711_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01712_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01713_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01714_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01715_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01716_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01717_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01718_checked
  apply FastArmCover.cells_cons_checked _ _ _ _ _ leaf01719_checked
  rfl
#print axioms chunk171_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
