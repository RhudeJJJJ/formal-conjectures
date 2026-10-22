/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerClassCell
import Proofs.RadenkovicGutmanD1Norm10Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def leaf00404 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack
  false (140031175567/1000000000000) (1415005128801537899833/1180591620717411303424) (427651533388984669033/4722366482869645213696)
  0 32 ![52,0,4]
  ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]
theorem leaf00404_checked : FastNestedCellData.accepts 1 0 4 leaf00404=true := by
  apply PackedIntegerClassCell.accepts_make
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00404_checked
def leaf00405 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack
  true (11670689677/100000000000) (1456733774860671181439/1180591620717411303424) (496276097492345859987/4722366482869645213696)
  0 32 ![52,0,4]
  ![(7/8),0,0] ![(1/8),1,(1/2)]
theorem leaf00405_checked : FastNestedCellData.accepts 1 0 4 leaf00405=true := by
  apply PackedIntegerClassCell.accepts_make
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00405_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
