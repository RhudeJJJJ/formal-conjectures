/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00807 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9075533496324510449838214610944000000000000 3594367790333609687313057360247603169591296 7305838578186234893580573343744000000000000))
theorem leaf00807_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9075533496324510449838214610944000000000000 3594367790333609687313057360247603169591296 7305838578186234893580573343744000000000000 raw00807=true := by decide +kernel
#print axioms leaf00807_raw
theorem leaf00807_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00807=true := by decide +kernel
#print axioms leaf00807_rectangular
def affine00807 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00807 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00807_transform : affine00807=(NestedInteger.clearedAll 3 raw00807 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00807_transform
theorem leaf00807_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00807=true := by decide +kernel
#print axioms leaf00807_sign
theorem leaf00807_log : RationalLog.accepts (1140106871/4294967296) (-1424127371/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00807_log
def leaf00807 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (491985656659/1000000000000) (1140106871/4294967296) (-1424127371/2147483648) 2 8 ![60,0,4] ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00807
theorem leaf00807_checked : FastNestedCellData.accepts 1 2 4 leaf00807=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (491985656659/1000000000000) (1140106871/4294967296) (-1424127371/2147483648) 2 8 ![60,0,4] ![(139/3200),0,(1/8)] ![(3/3200),1,(1/8)] 9075533496324510449838214610944000000000000 3594367790333609687313057360247603169591296 7305838578186234893580573343744000000000000 raw00807 affine00807
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00807_raw leaf00807_rectangular
    leaf00807_transform leaf00807_sign leaf00807_log
#print axioms leaf00807_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
