/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerClassCell
import Proofs.RadenkovicGutmanD1Norm10Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack
  false (1322830453/50000000000) (7589139995577183/4722366482869645213696) (-31500787239101063476977/4722366482869645213696)
  20 32 ![52,0,4]
  ![(1/1000),0,0] ![(1/4000),1,(1/4)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 0 4 leaf00000=true := by
  apply PackedIntegerClassCell.accepts_make
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00000_checked
def leaf00001 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack
  false (33302833/3906250000) (285625526111605066811/295147905179352825856) (-4839687859362562777/295147905179352825856)
  1 32 ![52,0,4]
  ![(1/1000),0,(1/4)] ![(1/4000),1,(1/4)]
theorem leaf00001_checked : FastNestedCellData.accepts 1 0 4 leaf00001=true := by
  apply PackedIntegerClassCell.accepts_make
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00001_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
