/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00822 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 584305789546801376781232242688000000000000 228239735610888127456506072068825248956416 450350662442815075007470764032000000000000))
theorem leaf00822_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 584305789546801376781232242688000000000000 228239735610888127456506072068825248956416 450350662442815075007470764032000000000000 raw00822=true := by decide +kernel
#print axioms leaf00822_raw
theorem leaf00822_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00822=true := by decide +kernel
#print axioms leaf00822_rectangular
def affine00822 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00822 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00822_transform : affine00822=(NestedInteger.clearedAll 3 raw00822 (IntegerComputedClassCell.leftNumerator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00822_transform
theorem leaf00822_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00822=true := by decide +kernel
#print axioms leaf00822_sign
theorem leaf00822_log : RationalLog.accepts (556703597/2147483648) (-362392997/536870912) 2 8=true := by decide +kernel
#print axioms leaf00822_log
def leaf00822 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (253402242569/500000000000) (556703597/2147483648) (-362392997/536870912) 2 8 ![60,0,4] ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)] affine00822
theorem leaf00822_checked : FastNestedCellData.accepts 1 2 4 leaf00822=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (253402242569/500000000000) (556703597/2147483648) (-362392997/536870912) 2 8 ![60,0,4] ![(37/800),0,(1/8)] ![(3/3200),1,(1/8)] 584305789546801376781232242688000000000000 228239735610888127456506072068825248956416 450350662442815075007470764032000000000000 raw00822 affine00822
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00822_raw leaf00822_rectangular
    leaf00822_transform leaf00822_sign leaf00822_log
#print axioms leaf00822_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
