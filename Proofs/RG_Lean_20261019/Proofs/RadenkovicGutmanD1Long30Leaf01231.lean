/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01231 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 142220891530609870935949312000000000000 157221738978867830992949915371261919232 19914479721212425009757159424000000000000))
theorem leaf01231_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 142220891530609870935949312000000000000 157221738978867830992949915371261919232 19914479721212425009757159424000000000000 raw01231=true := by decide +kernel
#print axioms leaf01231_raw
theorem leaf01231_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01231=true := by decide +kernel
#print axioms leaf01231_rectangular
def affine01231 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01231 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01231_transform : affine01231=(NestedInteger.clearedAll 3 raw01231 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01231_transform
theorem leaf01231_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01231=true := by decide +kernel
#print axioms leaf01231_sign
theorem leaf01231_log : RationalLog.accepts (294424437/268435456) (99226513/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01231_log
def leaf01231 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3947422709/500000000000) (294424437/268435456) (99226513/2147483648) 0 8 ![60,0,4] ![(17/64),0,(1/2)] ![(1/64),1,(1/4)] affine01231
theorem leaf01231_checked : FastNestedCellData.accepts 1 2 4 leaf01231=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3947422709/500000000000) (294424437/268435456) (99226513/2147483648) 0 8 ![60,0,4] ![(17/64),0,(1/2)] ![(1/64),1,(1/4)] 142220891530609870935949312000000000000 157221738978867830992949915371261919232 19914479721212425009757159424000000000000 raw01231 affine01231
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01231_raw leaf01231_rectangular
    leaf01231_transform leaf01231_sign leaf01231_log
#print axioms leaf01231_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
