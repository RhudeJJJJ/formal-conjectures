/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00479 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 2612453905627890630325698560000000000 2649621508217691500298659439593914368 7483674984503237187932698705920000000000))
theorem leaf00479_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 2612453905627890630325698560000000000 2649621508217691500298659439593914368 7483674984503237187932698705920000000000 raw00479=true := by decide +kernel
#print axioms leaf00479_raw
theorem leaf00479_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00479=true := by decide +kernel
#print axioms leaf00479_rectangular
def affine00479 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00479 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)]))
theorem leaf00479_transform : affine00479=(NestedInteger.clearedAll 3 raw00479 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/2)] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf00479_transform
theorem leaf00479_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00479=true := by decide +kernel
#print axioms leaf00479_sign
theorem leaf00479_log : RationalLog.accepts (2177265211/2147483648) (29576945/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00479_log
def leaf00479 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (14162141/40000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,(1/2)] ![(1/128),1,(1/2)] affine00479
theorem leaf00479_checked : FastNestedCellData.accepts 1 0 4 leaf00479=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (14162141/40000000000) (2177265211/2147483648) (29576945/4294967296) 0 8 ![52,0,4] ![(11/128),0,(1/2)] ![(1/128),1,(1/2)] 2612453905627890630325698560000000000 2649621508217691500298659439593914368 7483674984503237187932698705920000000000 raw00479 affine00479
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00479_raw leaf00479_rectangular
    leaf00479_transform leaf00479_sign leaf00479_log
#print axioms leaf00479_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
