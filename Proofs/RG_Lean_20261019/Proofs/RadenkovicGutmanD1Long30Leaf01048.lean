/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01048 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 63855998553097926799299444736000000000000 55176189509229242530382177993502880694272 142315336446441080372944961536000000000000))
theorem leaf01048_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 63855998553097926799299444736000000000000 55176189509229242530382177993502880694272 142315336446441080372944961536000000000000 raw01048=true := by decide +kernel
#print axioms leaf01048_raw
theorem leaf01048_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01048=true := by decide +kernel
#print axioms leaf01048_rectangular
def affine01048 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01048 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01048_transform : affine01048=(NestedInteger.clearedAll 3 raw01048 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01048_transform
theorem leaf01048_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01048=true := by decide +kernel
#print axioms leaf01048_sign
theorem leaf01048_log : RationalLog.accepts (1337159173/2147483648) (-508684581/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01048_log
def leaf01048 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (193851874601/500000000000) (1337159173/2147483648) (-508684581/2147483648) 1 8 ![60,0,4] ![(41/160),0,(1/4)] ![(3/160),1,(1/4)] affine01048
theorem leaf01048_checked : FastNestedCellData.accepts 1 2 4 leaf01048=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (193851874601/500000000000) (1337159173/2147483648) (-508684581/2147483648) 1 8 ![60,0,4] ![(41/160),0,(1/4)] ![(3/160),1,(1/4)] 63855998553097926799299444736000000000000 55176189509229242530382177993502880694272 142315336446441080372944961536000000000000 raw01048 affine01048
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01048_raw leaf01048_rectangular
    leaf01048_transform leaf01048_sign leaf01048_log
#print axioms leaf01048_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
