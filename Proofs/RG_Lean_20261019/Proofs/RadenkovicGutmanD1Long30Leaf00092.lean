/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00092 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 166459930933603558070681600000000000 153380742784759568132625377695629312 4414617163530758717964288000000000000))
theorem leaf00092_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 166459930933603558070681600000000000 153380742784759568132625377695629312 4414617163530758717964288000000000000 raw00092=true := by decide +kernel
#print axioms leaf00092_raw
theorem leaf00092_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00092=true := by decide +kernel
#print axioms leaf00092_rectangular
def affine00092 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00092 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00092_transform : affine00092=(NestedInteger.clearedAll 3 raw00092 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00092_transform
theorem leaf00092_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00092=true := by decide +kernel
#print axioms leaf00092_sign
theorem leaf00092_log : RationalLog.accepts (3824618655/4294967296) (-124538153/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00092_log
def leaf00092 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (271436233/7812500000) (3824618655/4294967296) (-124538153/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)] affine00092
theorem leaf00092_checked : FastNestedCellData.accepts 1 2 4 leaf00092=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (271436233/7812500000) (3824618655/4294967296) (-124538153/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/8)] ![(3/32000),1,(1/8)] 166459930933603558070681600000000000 153380742784759568132625377695629312 4414617163530758717964288000000000000 raw00092 affine00092
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00092_raw leaf00092_rectangular
    leaf00092_transform leaf00092_sign leaf00092_log
#print axioms leaf00092_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
