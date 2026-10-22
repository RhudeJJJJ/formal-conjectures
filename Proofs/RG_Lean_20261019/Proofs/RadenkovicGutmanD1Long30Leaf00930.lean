/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00930 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 47032576208008164466413377945600000000000 10690056038267644210969691556959135727616 13102403148684547405190791168000000000000))
theorem leaf00930_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 47032576208008164466413377945600000000000 10690056038267644210969691556959135727616 13102403148684547405190791168000000000000 raw00930=true := by decide +kernel
#print axioms leaf00930_raw
theorem leaf00930_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00930=true := by decide +kernel
#print axioms leaf00930_rectangular
def affine00930 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00930 (IntegerComputedClassCell.leftNumerator ![(27/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/320),0,0] ![(1/320),1,(1/16)]))
theorem leaf00930_transform : affine00930=(NestedInteger.clearedAll 3 raw00930 (IntegerComputedClassCell.leftNumerator ![(27/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/320),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00930_transform
theorem leaf00930_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00930=true := by decide +kernel
#print axioms leaf00930_sign
theorem leaf00930_log : RationalLog.accepts (67198985/536870912) (-4462684877/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00930_log
def leaf00930 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (815885140837/1000000000000) (67198985/536870912) (-4462684877/4294967296) 3 8 ![60,0,4] ![(27/320),0,0] ![(1/320),1,(1/16)] affine00930
theorem leaf00930_checked : FastNestedCellData.accepts 1 2 4 leaf00930=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (815885140837/1000000000000) (67198985/536870912) (-4462684877/4294967296) 3 8 ![60,0,4] ![(27/320),0,0] ![(1/320),1,(1/16)] 47032576208008164466413377945600000000000 10690056038267644210969691556959135727616 13102403148684547405190791168000000000000 raw00930 affine00930
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00930_raw leaf00930_rectangular
    leaf00930_transform leaf00930_sign leaf00930_log
#print axioms leaf00930_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
