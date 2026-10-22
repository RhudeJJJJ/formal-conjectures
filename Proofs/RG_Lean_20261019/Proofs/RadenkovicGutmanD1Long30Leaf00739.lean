/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00739 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 854858539966992787390290984960000000000 670534152521905121125503258292748550144 5787704667362111108343094312960000000000))
theorem leaf00739_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 854858539966992787390290984960000000000 670534152521905121125503258292748550144 5787704667362111108343094312960000000000 raw00739=true := by decide +kernel
#print axioms leaf00739_raw
theorem leaf00739_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00739=true := by decide +kernel
#print axioms leaf00739_rectangular
def affine00739 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00739 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00739_transform : affine00739=(NestedInteger.clearedAll 3 raw00739 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00739_transform
theorem leaf00739_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00739=true := by decide +kernel
#print axioms leaf00739_sign
theorem leaf00739_log : RationalLog.accepts (1509554423/2147483648) (-189237469/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00739_log
def leaf00739 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4634197431/40000000000) (1509554423/2147483648) (-189237469/1073741824) 1 8 ![60,0,4] ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00739
theorem leaf00739_checked : FastNestedCellData.accepts 1 2 4 leaf00739=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4634197431/40000000000) (1509554423/2147483648) (-189237469/1073741824) 1 8 ![60,0,4] ![(103/3200),0,(1/2)] ![(3/6400),1,(1/2)] 854858539966992787390290984960000000000 670534152521905121125503258292748550144 5787704667362111108343094312960000000000 raw00739 affine00739
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00739_raw leaf00739_rectangular
    leaf00739_transform leaf00739_sign leaf00739_log
#print axioms leaf00739_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
