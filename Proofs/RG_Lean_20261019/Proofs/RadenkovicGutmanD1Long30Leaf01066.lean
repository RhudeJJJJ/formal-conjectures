/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01066 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 259381484026803941327608217600000000000 258273125913173740416257500895036571648 717496860956927243586424012800000000000))
theorem leaf01066_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 259381484026803941327608217600000000000 258273125913173740416257500895036571648 717496860956927243586424012800000000000 raw01066=true := by decide +kernel
#print axioms leaf01066_raw
theorem leaf01066_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01066=true := by decide +kernel
#print axioms leaf01066_rectangular
def affine01066 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01066 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01066_transform : affine01066=(NestedInteger.clearedAll 3 raw01066 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01066_transform
theorem leaf01066_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01066=true := by decide +kernel
#print axioms leaf01066_sign
theorem leaf01066_log : RationalLog.accepts (393081561/536870912) (-669457777/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01066_log
def leaf01066 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17998205983/50000000000) (393081561/536870912) (-669457777/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/16)] ![(3/160),1,(1/16)] affine01066
theorem leaf01066_checked : FastNestedCellData.accepts 1 2 4 leaf01066=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17998205983/50000000000) (393081561/536870912) (-669457777/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/16)] ![(3/160),1,(1/16)] 259381484026803941327608217600000000000 258273125913173740416257500895036571648 717496860956927243586424012800000000000 raw01066 affine01066
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01066_raw leaf01066_rectangular
    leaf01066_transform leaf01066_sign leaf01066_log
#print axioms leaf01066_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
