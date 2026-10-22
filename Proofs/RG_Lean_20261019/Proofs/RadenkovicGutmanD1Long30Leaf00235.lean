/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00235 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7784112164277032115586050555904000000000000 4502554586672242952753824953369710559232 10670127868842716905684860928000000000000))
theorem leaf00235_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7784112164277032115586050555904000000000000 4502554586672242952753824953369710559232 10670127868842716905684860928000000000000 raw00235=true := by decide +kernel
#print axioms leaf00235_raw
theorem leaf00235_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00235=true := by decide +kernel
#print axioms leaf00235_rectangular
def affine00235 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00235 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00235_transform : affine00235=(NestedInteger.clearedAll 3 raw00235 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00235_transform
theorem leaf00235_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00235=true := by decide +kernel
#print axioms leaf00235_sign
theorem leaf00235_log : RationalLog.accepts (1747097/4294967296) (-16765928533/4294967296) 12 8=true := by decide +kernel
#print axioms leaf00235_log
def leaf00235 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (421977565969/1000000000000) (1747097/4294967296) (-16765928533/4294967296) 12 8 ![60,0,4] ![(157/32000),0,0] ![(3/32000),1,(1/16)] affine00235
theorem leaf00235_checked : FastNestedCellData.accepts 1 2 4 leaf00235=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (421977565969/1000000000000) (1747097/4294967296) (-16765928533/4294967296) 12 8 ![60,0,4] ![(157/32000),0,0] ![(3/32000),1,(1/16)] 7784112164277032115586050555904000000000000 4502554586672242952753824953369710559232 10670127868842716905684860928000000000000 raw00235 affine00235
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00235_raw leaf00235_rectangular
    leaf00235_transform leaf00235_sign leaf00235_log
#print axioms leaf00235_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
