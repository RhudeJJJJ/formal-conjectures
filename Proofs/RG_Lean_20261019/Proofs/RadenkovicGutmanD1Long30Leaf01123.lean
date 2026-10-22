/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01123 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 28934225828088734972475185561600000000000 35390953656889980605007566361988454940672 225631702922354923773390697267200000000000))
theorem leaf01123_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 28934225828088734972475185561600000000000 35390953656889980605007566361988454940672 225631702922354923773390697267200000000000 raw01123=true := by decide +kernel
#print axioms leaf01123_raw
theorem leaf01123_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01123=true := by decide +kernel
#print axioms leaf01123_rectangular
def affine01123 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01123 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01123_transform : affine01123=(NestedInteger.clearedAll 3 raw01123 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01123_transform
theorem leaf01123_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01123=true := by decide +kernel
#print axioms leaf01123_sign
theorem leaf01123_log : RationalLog.accepts (4541111607/4294967296) (119674729/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01123_log
def leaf01123 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15685275251/100000000000) (4541111607/4294967296) (119674729/4294967296) 0 8 ![60,0,4] ![(11/16),0,(7/8)] ![(1/16),1,(1/16)] affine01123
theorem leaf01123_checked : FastNestedCellData.accepts 1 2 4 leaf01123=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15685275251/100000000000) (4541111607/4294967296) (119674729/4294967296) 0 8 ![60,0,4] ![(11/16),0,(7/8)] ![(1/16),1,(1/16)] 28934225828088734972475185561600000000000 35390953656889980605007566361988454940672 225631702922354923773390697267200000000000 raw01123 affine01123
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01123_raw leaf01123_rectangular
    leaf01123_transform leaf01123_sign leaf01123_log
#print axioms leaf01123_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
