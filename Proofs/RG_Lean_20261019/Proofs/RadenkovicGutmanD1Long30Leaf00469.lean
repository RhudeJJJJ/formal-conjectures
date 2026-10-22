/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00469 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 51309328334235336311228596224000000000000 46369136127972209858842377866206110547968 1041915299372786878167155474432000000000000))
theorem leaf00469_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 51309328334235336311228596224000000000000 46369136127972209858842377866206110547968 1041915299372786878167155474432000000000000 raw00469=true := by decide +kernel
#print axioms leaf00469_raw
theorem leaf00469_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00469=true := by decide +kernel
#print axioms leaf00469_rectangular
def affine00469 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00469 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00469_transform : affine00469=(NestedInteger.clearedAll 3 raw00469 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00469_transform
theorem leaf00469_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00469=true := by decide +kernel
#print axioms leaf00469_sign
theorem leaf00469_log : RationalLog.accepts (929014607/1073741824) (-155456785/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00469_log
def leaf00469 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (44503748199/1000000000000) (929014607/1073741824) (-155456785/2147483648) 1 8 ![60,0,4] ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00469
theorem leaf00469_checked : FastNestedCellData.accepts 1 2 4 leaf00469=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (44503748199/1000000000000) (929014607/1073741824) (-155456785/2147483648) 1 8 ![60,0,4] ![(77/6400),0,(1/2)] ![(1/6400),1,(1/2)] 51309328334235336311228596224000000000000 46369136127972209858842377866206110547968 1041915299372786878167155474432000000000000 raw00469 affine00469
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00469_raw leaf00469_rectangular
    leaf00469_transform leaf00469_sign leaf00469_log
#print axioms leaf00469_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
