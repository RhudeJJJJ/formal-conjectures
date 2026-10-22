/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00582 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25813996332057883316372635648000000000000 14602639034297130427971059019983930523648 54349380694123060158684725248000000000000))
theorem leaf00582_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25813996332057883316372635648000000000000 14602639034297130427971059019983930523648 54349380694123060158684725248000000000000 raw00582=true := by decide +kernel
#print axioms leaf00582_raw
theorem leaf00582_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00582=true := by decide +kernel
#print axioms leaf00582_rectangular
def affine00582 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00582 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00582_transform : affine00582=(NestedInteger.clearedAll 3 raw00582 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00582_transform
theorem leaf00582_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00582=true := by decide +kernel
#print axioms leaf00582_sign
theorem leaf00582_log : RationalLog.accepts (957532623/2147483648) (-867252983/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00582_log
def leaf00582 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67170218169/250000000000) (957532623/2147483648) (-867252983/2147483648) 2 8 ![60,0,4] ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00582
theorem leaf00582_checked : FastNestedCellData.accepts 1 2 4 leaf00582=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67170218169/250000000000) (957532623/2147483648) (-867252983/2147483648) 2 8 ![60,0,4] ![(59/3200),0,(1/8)] ![(1/3200),1,(1/8)] 25813996332057883316372635648000000000000 14602639034297130427971059019983930523648 54349380694123060158684725248000000000000 raw00582 affine00582
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00582_raw leaf00582_rectangular
    leaf00582_transform leaf00582_sign leaf00582_log
#print axioms leaf00582_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
