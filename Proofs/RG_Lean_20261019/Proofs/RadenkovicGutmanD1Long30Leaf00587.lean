/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00587 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1256926027625368786264070815744000000000000 705886019821191164841562293683172927340544 2589909522649336249893942984704000000000000))
theorem leaf00587_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1256926027625368786264070815744000000000000 705886019821191164841562293683172927340544 2589909522649336249893942984704000000000000 raw00587=true := by decide +kernel
#print axioms leaf00587_raw
theorem leaf00587_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00587=true := by decide +kernel
#print axioms leaf00587_rectangular
def affine00587 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00587 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00587_transform : affine00587=(NestedInteger.clearedAll 3 raw00587 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00587_transform
theorem leaf00587_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00587=true := by decide +kernel
#print axioms leaf00587_sign
theorem leaf00587_log : RationalLog.accepts (947717843/2147483648) (-439157855/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00587_log
def leaf00587 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (272552385961/1000000000000) (947717843/2147483648) (-439157855/1073741824) 2 8 ![60,0,4] ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)] affine00587
theorem leaf00587_checked : FastNestedCellData.accepts 1 2 4 leaf00587=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (272552385961/1000000000000) (947717843/2147483648) (-439157855/1073741824) 2 8 ![60,0,4] ![(3/160),0,(1/8)] ![(1/3200),1,(1/8)] 1256926027625368786264070815744000000000000 705886019821191164841562293683172927340544 2589909522649336249893942984704000000000000 raw00587 affine00587
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00587_raw leaf00587_rectangular
    leaf00587_transform leaf00587_sign leaf00587_log
#print axioms leaf00587_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
