/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01354 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 175649435901260507748761600000000000 175734849777769368428477063840661504 76898809410936880404046544896000000000000))
theorem leaf01354_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 175649435901260507748761600000000000 175734849777769368428477063840661504 76898809410936880404046544896000000000000 raw01354=true := by decide +kernel
#print axioms leaf01354_raw
theorem leaf01354_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01354=true := by decide +kernel
#print axioms leaf01354_rectangular
def affine01354 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01354 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/512),1,1]))
theorem leaf01354_transform : affine01354=(NestedInteger.clearedAll 3 raw01354 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01354_transform
theorem leaf01354_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01354=true := by decide +kernel
#print axioms leaf01354_sign
theorem leaf01354_log : RationalLog.accepts (2148523005/2147483648) (1039105/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01354_log
def leaf01354 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1142637/500000000000) (2148523005/2147483648) (1039105/4294967296) 0 8 ![60,0,4] ![(1/64),0,0] ![(1/512),1,1] affine01354
theorem leaf01354_checked : FastNestedCellData.accepts 1 2 4 leaf01354=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1142637/500000000000) (2148523005/2147483648) (1039105/4294967296) 0 8 ![60,0,4] ![(1/64),0,0] ![(1/512),1,1] 175649435901260507748761600000000000 175734849777769368428477063840661504 76898809410936880404046544896000000000000 raw01354 affine01354
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01354_raw leaf01354_rectangular
    leaf01354_transform leaf01354_sign leaf01354_log
#print axioms leaf01354_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
