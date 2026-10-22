/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01097 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1015796885321888202346511466496000000000000 1157083560963516240570395237406278886096896 5253123097100955987078759317504000000000000))
theorem leaf01097_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1015796885321888202346511466496000000000000 1157083560963516240570395237406278886096896 5253123097100955987078759317504000000000000 raw01097=true := by decide +kernel
#print axioms leaf01097_raw
theorem leaf01097_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01097=true := by decide +kernel
#print axioms leaf01097_rectangular
def affine01097 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01097 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01097_transform : affine01097=(NestedInteger.clearedAll 3 raw01097 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01097_transform
theorem leaf01097_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01097=true := by decide +kernel
#print axioms leaf01097_sign
theorem leaf01097_log : RationalLog.accepts (4009251079/4294967296) (-147831695/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01097_log
def leaf01097 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (110132918987/500000000000) (4009251079/4294967296) (-147831695/4294967296) 1 8 ![60,0,4] ![(1/2),0,(3/4)] ![(1/32),1,(1/8)] affine01097
theorem leaf01097_checked : FastNestedCellData.accepts 1 2 4 leaf01097=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (110132918987/500000000000) (4009251079/4294967296) (-147831695/4294967296) 1 8 ![60,0,4] ![(1/2),0,(3/4)] ![(1/32),1,(1/8)] 1015796885321888202346511466496000000000000 1157083560963516240570395237406278886096896 5253123097100955987078759317504000000000000 raw01097 affine01097
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01097_raw leaf01097_rectangular
    leaf01097_transform leaf01097_sign leaf01097_log
#print axioms leaf01097_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
