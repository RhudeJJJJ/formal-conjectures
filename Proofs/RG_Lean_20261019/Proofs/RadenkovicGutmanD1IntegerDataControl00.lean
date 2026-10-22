/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration
import Proofs.RadenkovicGutmanD1Norm00Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificate00000 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)])
theorem leaf00000_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]=certificate00000 := by rfl
#print axioms leaf00000_identity
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] certificate00000=true := by decide +kernel
#print axioms leaf00000_sign
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)] certificate00000
    leaf00000_identity ?_ ?_ ?_ leaf00000_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00000_checked
def certificate01753 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1])
theorem leaf01753_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1]=certificate01753 := by rfl
#print axioms leaf01753_identity
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] certificate01753=true := by decide +kernel
#print axioms leaf01753_sign
def leaf01753 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1]
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] certificate01753
    leaf01753_identity ?_ ?_ ?_ leaf01753_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl00
