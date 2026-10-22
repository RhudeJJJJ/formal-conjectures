/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00501 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 936693427086430138459362426880000000000 408525900048435538962420273087799885824 1072705684023834214131816202240000000000))
theorem leaf00501_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 936693427086430138459362426880000000000 408525900048435538962420273087799885824 1072705684023834214131816202240000000000 raw00501=true := by decide +kernel
#print axioms leaf00501_raw
theorem leaf00501_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00501=true := by decide +kernel
#print axioms leaf00501_rectangular
def affine00501 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00501 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00501_transform : affine00501=(NestedInteger.clearedAll 3 raw00501 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00501_transform
theorem leaf00501_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00501=true := by decide +kernel
#print axioms leaf00501_sign
theorem leaf00501_log : RationalLog.accepts (678280929/2147483648) (-618738637/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00501_log
def leaf00501 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15233475729/40000000000) (678280929/2147483648) (-618738637/1073741824) 2 8 ![60,0,4] ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00501
theorem leaf00501_checked : FastNestedCellData.accepts 1 2 4 leaf00501=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15233475729/40000000000) (678280929/2147483648) (-618738637/1073741824) 2 8 ![60,0,4] ![(43/3200),0,(1/16)] ![(1/3200),1,(1/16)] 936693427086430138459362426880000000000 408525900048435538962420273087799885824 1072705684023834214131816202240000000000 raw00501 affine00501
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00501_raw leaf00501_rectangular
    leaf00501_transform leaf00501_sign leaf00501_log
#print axioms leaf00501_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
