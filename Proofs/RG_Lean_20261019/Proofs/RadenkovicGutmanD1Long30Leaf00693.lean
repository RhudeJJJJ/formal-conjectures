/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00693 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 46561751689512445562217247539200000000000 30677307528128330504330019033563715862528 151920949144974133511027949568000000000000))
theorem leaf00693_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 46561751689512445562217247539200000000000 30677307528128330504330019033563715862528 151920949144974133511027949568000000000000 raw00693=true := by decide +kernel
#print axioms leaf00693_raw
theorem leaf00693_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00693=true := by decide +kernel
#print axioms leaf00693_rectangular
def affine00693 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00693 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00693_transform : affine00693=(NestedInteger.clearedAll 3 raw00693 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00693_transform
theorem leaf00693_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00693=true := by decide +kernel
#print axioms leaf00693_sign
theorem leaf00693_log : RationalLog.accepts (1177169045/2147483648) (-645516765/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00693_log
def leaf00693 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (100964704673/500000000000) (1177169045/2147483648) (-645516765/2147483648) 1 8 ![60,0,4] ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00693
theorem leaf00693_checked : FastNestedCellData.accepts 1 2 4 leaf00693=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (100964704673/500000000000) (1177169045/2147483648) (-645516765/2147483648) 1 8 ![60,0,4] ![(179/6400),0,(1/4)] ![(3/6400),1,(1/4)] 46561751689512445562217247539200000000000 30677307528128330504330019033563715862528 151920949144974133511027949568000000000000 raw00693 affine00693
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00693_raw leaf00693_rectangular
    leaf00693_transform leaf00693_sign leaf00693_log
#print axioms leaf00693_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
