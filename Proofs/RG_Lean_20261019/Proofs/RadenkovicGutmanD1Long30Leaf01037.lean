/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01037 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 344464894583111724590779963801600000000000 267480804905982006503586438362364362358784 572964041366483410741051890073600000000000))
theorem leaf01037_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 344464894583111724590779963801600000000000 267480804905982006503586438362364362358784 572964041366483410741051890073600000000000 raw01037=true := by decide +kernel
#print axioms leaf01037_raw
theorem leaf01037_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01037=true := by decide +kernel
#print axioms leaf01037_rectangular
def affine01037 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01037 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01037_transform : affine01037=(NestedInteger.clearedAll 3 raw01037 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01037_transform
theorem leaf01037_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01037=true := by decide +kernel
#print axioms leaf01037_sign
theorem leaf01037_log : RationalLog.accepts (2273660741/4294967296) (-682956455/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01037_log
def leaf01037 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93367396763/200000000000) (2273660741/4294967296) (-682956455/2147483648) 1 8 ![60,0,4] ![(7/32),0,(1/8)] ![(3/160),1,(1/8)] affine01037
theorem leaf01037_checked : FastNestedCellData.accepts 1 2 4 leaf01037=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93367396763/200000000000) (2273660741/4294967296) (-682956455/2147483648) 1 8 ![60,0,4] ![(7/32),0,(1/8)] ![(3/160),1,(1/8)] 344464894583111724590779963801600000000000 267480804905982006503586438362364362358784 572964041366483410741051890073600000000000 raw01037 affine01037
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01037_raw leaf01037_rectangular
    leaf01037_transform leaf01037_sign leaf01037_log
#print axioms leaf01037_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
