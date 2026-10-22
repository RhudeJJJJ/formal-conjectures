/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration
import Proofs.RadenkovicGutmanD1Norm30Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificate00000 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)])
theorem leaf00000_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)]=certificate00000 := by rfl
#print axioms leaf00000_identity
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] certificate00000=true := by decide +kernel
#print axioms leaf00000_sign
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 2 4 leaf00000=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)] certificate00000
    leaf00000_identity ?_ ?_ ?_ leaf00000_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00000_checked
def certificate01365 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1])
theorem leaf01365_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1]=certificate01365 := by rfl
#print axioms leaf01365_identity
theorem leaf01365_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] certificate01365=true := by decide +kernel
#print axioms leaf01365_sign
def leaf01365 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1]
theorem leaf01365_checked : FastNestedCellData.accepts 1 2 4 leaf01365=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1] certificate01365
    leaf01365_identity ?_ ?_ ?_ leaf01365_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf01365_checked
end Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl30
