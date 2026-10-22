/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01062 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6761668093482827074918798065664000000000000 6520659398620747995840235295439036899917824 17789239793376034505440578502656000000000000))
theorem leaf01062_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6761668093482827074918798065664000000000000 6520659398620747995840235295439036899917824 17789239793376034505440578502656000000000000 raw01062=true := by decide +kernel
#print axioms leaf01062_raw
theorem leaf01062_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01062=true := by decide +kernel
#print axioms leaf01062_rectangular
def affine01062 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01062 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01062_transform : affine01062=(NestedInteger.clearedAll 3 raw01062 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01062_transform
theorem leaf01062_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01062=true := by decide +kernel
#print axioms leaf01062_sign
theorem leaf01062_log : RationalLog.accepts (3030901059/4294967296) (-748578447/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01062_log
def leaf01062 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (366550761829/1000000000000) (3030901059/4294967296) (-748578447/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/8)] ![(3/160),1,(1/8)] affine01062
theorem leaf01062_checked : FastNestedCellData.accepts 1 2 4 leaf01062=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (366550761829/1000000000000) (3030901059/4294967296) (-748578447/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/8)] ![(3/160),1,(1/8)] 6761668093482827074918798065664000000000000 6520659398620747995840235295439036899917824 17789239793376034505440578502656000000000000 raw01062 affine01062
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01062_raw leaf01062_rectangular
    leaf01062_transform leaf01062_sign leaf01062_log
#print axioms leaf01062_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
