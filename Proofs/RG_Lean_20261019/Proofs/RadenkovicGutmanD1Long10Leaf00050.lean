/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00050 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4581791115684575567922017075200000000000 4363166733691688787483932413138235817984 219581758681146786043222032384000000000000))
theorem leaf00050_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4581791115684575567922017075200000000000 4363166733691688787483932413138235817984 219581758681146786043222032384000000000000 raw00050=true := by decide +kernel
#print axioms leaf00050_raw
theorem leaf00050_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00050=true := by decide +kernel
#print axioms leaf00050_rectangular
def affine00050 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00050 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00050_transform : affine00050=(NestedInteger.clearedAll 3 raw00050 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00050_transform
theorem leaf00050_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00050=true := by decide +kernel
#print axioms leaf00050_sign
theorem leaf00050_log : RationalLog.accepts (2005171035/2147483648) (-36811851/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00050_log
def leaf00050 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9935175763/500000000000) (2005171035/2147483648) (-36811851/1073741824) 1 8 ![52,0,4] ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00050
theorem leaf00050_checked : FastNestedCellData.accepts 1 0 4 leaf00050=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9935175763/500000000000) (2005171035/2147483648) (-36811851/1073741824) 1 8 ![52,0,4] ![(17/3200),0,(1/2)] ![(1/3200),1,(1/2)] 4581791115684575567922017075200000000000 4363166733691688787483932413138235817984 219581758681146786043222032384000000000000 raw00050 affine00050
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00050_raw leaf00050_rectangular
    leaf00050_transform leaf00050_sign leaf00050_log
#print axioms leaf00050_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
