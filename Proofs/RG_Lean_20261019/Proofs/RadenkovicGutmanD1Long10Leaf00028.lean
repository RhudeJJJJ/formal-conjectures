/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00028 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1323451957556084112337194188800000000000 1251423109852667382692508970048932544512 54508688678635899739189542912000000000000))
theorem leaf00028_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1323451957556084112337194188800000000000 1251423109852667382692508970048932544512 54508688678635899739189542912000000000000 raw00028=true := by decide +kernel
#print axioms leaf00028_raw
theorem leaf00028_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00028=true := by decide +kernel
#print axioms leaf00028_rectangular
def affine00028 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00028 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00028_transform : affine00028=(NestedInteger.clearedAll 3 raw00028 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00028_transform
theorem leaf00028_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00028=true := by decide +kernel
#print axioms leaf00028_sign
theorem leaf00028_log : RationalLog.accepts (496258505/536870912) (-42230655/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00028_log
def leaf00028 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (22958231801/1000000000000) (496258505/536870912) (-42230655/1073741824) 1 8 ![52,0,4] ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)] affine00028
theorem leaf00028_checked : FastNestedCellData.accepts 1 0 4 leaf00028=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (22958231801/1000000000000) (496258505/536870912) (-42230655/1073741824) 1 8 ![52,0,4] ![(47/16000),0,(1/4)] ![(3/16000),1,(1/4)] 1323451957556084112337194188800000000000 1251423109852667382692508970048932544512 54508688678635899739189542912000000000000 raw00028 affine00028
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00028_raw leaf00028_rectangular
    leaf00028_transform leaf00028_sign leaf00028_log
#print axioms leaf00028_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
