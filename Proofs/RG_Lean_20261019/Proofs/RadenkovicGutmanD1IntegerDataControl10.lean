/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerDataElaboration
import Proofs.RadenkovicGutmanD1Norm10Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificate00406 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)])
theorem leaf00406_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]=certificate00406 := by decide +kernel
#print axioms leaf00406_identity
theorem leaf00406_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] certificate00406=true := by decide +kernel
#print axioms leaf00406_sign
def leaf00406 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]
theorem leaf00406_checked : FastNestedCellData.accepts 1 0 4 leaf00406=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)] certificate00406
    leaf00406_identity ?_ ?_ ?_ leaf00406_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00406_checked
def certificate00407 : NestedInteger.Poly 3 := rg_integer_data%
  (PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)])
theorem leaf00407_identity : PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]=certificate00407 := by decide +kernel
#print axioms leaf00407_identity
theorem leaf00407_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] certificate00407=true := by decide +kernel
#print axioms leaf00407_sign
def leaf00407 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]
theorem leaf00407_checked : FastNestedCellData.accepts 1 0 4 leaf00407=true := by
  refine IntegerLiteral.accepts_materialized DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)] certificate00407
    leaf00407_identity ?_ ?_ ?_ leaf00407_sign ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
#print axioms leaf00407_checked
end Gebendorfer.RadenkovicGutman.DegreeOneIntegerDataControl10
