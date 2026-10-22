/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01232 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 72817080110633632575688540160000000000 80497511249118785950135463226845954048 10196213486773718866997962342400000000000))
theorem leaf01232_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 72817080110633632575688540160000000000 80497511249118785950135463226845954048 10196213486773718866997962342400000000000 raw01232=true := by decide +kernel
#print axioms leaf01232_raw
theorem leaf01232_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01232=true := by decide +kernel
#print axioms leaf01232_rectangular
def affine01232 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01232 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01232_transform : affine01232=(NestedInteger.clearedAll 3 raw01232 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/64),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01232_transform
theorem leaf01232_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01232=true := by decide +kernel
#print axioms leaf01232_sign
theorem leaf01232_log : RationalLog.accepts (1177697735/1073741824) (99226501/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01232_log
def leaf01232 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1578968729/200000000000) (1177697735/1073741824) (99226501/2147483648) 0 8 ![60,0,4] ![(17/64),0,(3/4)] ![(1/64),1,(1/8)] affine01232
theorem leaf01232_checked : FastNestedCellData.accepts 1 2 4 leaf01232=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1578968729/200000000000) (1177697735/1073741824) (99226501/2147483648) 0 8 ![60,0,4] ![(17/64),0,(3/4)] ![(1/64),1,(1/8)] 72817080110633632575688540160000000000 80497511249118785950135463226845954048 10196213486773718866997962342400000000000 raw01232 affine01232
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01232_raw leaf01232_rectangular
    leaf01232_transform leaf01232_sign leaf01232_log
#print axioms leaf01232_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
