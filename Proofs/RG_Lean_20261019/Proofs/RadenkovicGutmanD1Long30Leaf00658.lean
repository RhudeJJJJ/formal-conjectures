/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00658 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2084378476381640201664357990400000000000 1424828169565319904590302226274066628608 7881078487785606352234296115200000000000))
theorem leaf00658_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2084378476381640201664357990400000000000 1424828169565319904590302226274066628608 7881078487785606352234296115200000000000 raw00658=true := by decide +kernel
#print axioms leaf00658_raw
theorem leaf00658_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00658=true := by decide +kernel
#print axioms leaf00658_rectangular
def affine00658 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00658 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00658_transform : affine00658=(NestedInteger.clearedAll 3 raw00658 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00658_transform
theorem leaf00658_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00658=true := by decide +kernel
#print axioms leaf00658_sign
theorem leaf00658_log : RationalLog.accepts (621602487/1073741824) (-586911657/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00658_log
def leaf00658 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18079101379/100000000000) (621602487/1073741824) (-586911657/2147483648) 1 8 ![60,0,4] ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00658
theorem leaf00658_checked : FastNestedCellData.accepts 1 2 4 leaf00658=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18079101379/100000000000) (621602487/1073741824) (-586911657/2147483648) 1 8 ![60,0,4] ![(79/3200),0,(1/4)] ![(3/6400),1,(1/4)] 2084378476381640201664357990400000000000 1424828169565319904590302226274066628608 7881078487785606352234296115200000000000 raw00658 affine00658
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00658_raw leaf00658_rectangular
    leaf00658_transform leaf00658_sign leaf00658_log
#print axioms leaf00658_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
