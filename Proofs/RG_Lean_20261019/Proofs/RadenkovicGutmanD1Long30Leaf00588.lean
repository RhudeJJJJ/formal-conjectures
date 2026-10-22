/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00588 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2582040970460634402835761463296000000000000 1907340264887635207998312051716846681849856 13626514114370055855285653733376000000000000))
theorem leaf00588_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2582040970460634402835761463296000000000000 1907340264887635207998312051716846681849856 13626514114370055855285653733376000000000000 raw00588=true := by decide +kernel
#print axioms leaf00588_raw
theorem leaf00588_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00588=true := by decide +kernel
#print axioms leaf00588_rectangular
def affine00588 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00588 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00588_transform : affine00588=(NestedInteger.clearedAll 3 raw00588 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00588_transform
theorem leaf00588_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00588=true := by decide +kernel
#print axioms leaf00588_sign
theorem leaf00588_log : RationalLog.accepts (2783110501/4294967296) (-465869487/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00588_log
def leaf00588 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (139972721481/1000000000000) (2783110501/4294967296) (-465869487/2147483648) 1 8 ![60,0,4] ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)] affine00588
theorem leaf00588_checked : FastNestedCellData.accepts 1 2 4 leaf00588=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (139972721481/1000000000000) (2783110501/4294967296) (-465869487/2147483648) 1 8 ![60,0,4] ![(3/160),0,(1/4)] ![(1/3200),1,(1/4)] 2582040970460634402835761463296000000000000 1907340264887635207998312051716846681849856 13626514114370055855285653733376000000000000 raw00588 affine00588
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00588_raw leaf00588_rectangular
    leaf00588_transform leaf00588_sign leaf00588_log
#print axioms leaf00588_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
