/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00410 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3132822498555187164846548320256000000000000 10896547522961153594286979569556333264896 16040313769434683838157553664000000000000))
theorem leaf00410_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3132822498555187164846548320256000000000000 10896547522961153594286979569556333264896 16040313769434683838157553664000000000000 raw00410=true := by decide +kernel
#print axioms leaf00410_raw
theorem leaf00410_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00410=true := by decide +kernel
#print axioms leaf00410_rectangular
def affine00410 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00410 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00410_transform : affine00410=(NestedInteger.clearedAll 3 raw00410 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00410_transform
theorem leaf00410_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00410=true := by decide +kernel
#print axioms leaf00410_sign
theorem leaf00410_log : RationalLog.accepts (4447837/2147483648) (-1658832945/536870912) 9 8=true := by decide +kernel
#print axioms leaf00410_log
def leaf00410 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (679322591789/1000000000000) (4447837/2147483648) (-1658832945/536870912) 9 8 ![60,0,4] ![(33/3200),0,0] ![(1/6400),1,(1/16)] affine00410
theorem leaf00410_checked : FastNestedCellData.accepts 1 2 4 leaf00410=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (679322591789/1000000000000) (4447837/2147483648) (-1658832945/536870912) 9 8 ![60,0,4] ![(33/3200),0,0] ![(1/6400),1,(1/16)] 3132822498555187164846548320256000000000000 10896547522961153594286979569556333264896 16040313769434683838157553664000000000000 raw00410 affine00410
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00410_raw leaf00410_rectangular
    leaf00410_transform leaf00410_sign leaf00410_log
#print axioms leaf00410_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
