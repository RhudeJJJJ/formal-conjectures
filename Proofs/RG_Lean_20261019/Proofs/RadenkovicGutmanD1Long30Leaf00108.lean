/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00108 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 70675782982739305916951796121600000000000 67532538151066779658350151655052338528256 3525268190449331694981781389312000000000000))
theorem leaf00108_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 70675782982739305916951796121600000000000 67532538151066779658350151655052338528256 3525268190449331694981781389312000000000000 raw00108=true := by decide +kernel
#print axioms leaf00108_raw
theorem leaf00108_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00108=true := by decide +kernel
#print axioms leaf00108_rectangular
def affine00108 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00108 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00108_transform : affine00108=(NestedInteger.clearedAll 3 raw00108 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00108_transform
theorem leaf00108_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00108=true := by decide +kernel
#print axioms leaf00108_sign
theorem leaf00108_log : RationalLog.accepts (4026811845/4294967296) (-34611531/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00108_log
def leaf00108 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19156709363/1000000000000) (4026811845/4294967296) (-34611531/1073741824) 1 8 ![60,0,4] ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00108
theorem leaf00108_checked : FastNestedCellData.accepts 1 2 4 leaf00108=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19156709363/1000000000000) (4026811845/4294967296) (-34611531/1073741824) 1 8 ![60,0,4] ![(79/32000),0,(1/4)] ![(3/32000),1,(1/4)] 70675782982739305916951796121600000000000 67532538151066779658350151655052338528256 3525268190449331694981781389312000000000000 raw00108 affine00108
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00108_raw leaf00108_rectangular
    leaf00108_transform leaf00108_sign leaf00108_log
#print axioms leaf00108_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
