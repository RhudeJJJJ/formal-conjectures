/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01268 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 11293768954483172808053279948800000000000 11967861538350821850001432010827971428352 3909555433572305153169479958528000000000000))
theorem leaf01268_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 11293768954483172808053279948800000000000 11967861538350821850001432010827971428352 3909555433572305153169479958528000000000000 raw01268=true := by decide +kernel
#print axioms leaf01268_raw
theorem leaf01268_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01268=true := by decide +kernel
#print axioms leaf01268_rectangular
def affine01268 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01268 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01268_transform : affine01268=(NestedInteger.clearedAll 3 raw01268 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01268_transform
theorem leaf01268_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01268=true := by decide +kernel
#print axioms leaf01268_sign
theorem leaf01268_log : RationalLog.accepts (4537431635/4294967296) (117933771/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01268_log
def leaf01268 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3061182209/1000000000000) (4537431635/4294967296) (117933771/4294967296) 0 8 ![60,0,4] ![(3/16),0,(7/8)] ![(1/128),1,(1/16)] affine01268
theorem leaf01268_checked : FastNestedCellData.accepts 1 2 4 leaf01268=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3061182209/1000000000000) (4537431635/4294967296) (117933771/4294967296) 0 8 ![60,0,4] ![(3/16),0,(7/8)] ![(1/128),1,(1/16)] 11293768954483172808053279948800000000000 11967861538350821850001432010827971428352 3909555433572305153169479958528000000000000 raw01268 affine01268
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01268_raw leaf01268_rectangular
    leaf01268_transform leaf01268_sign leaf01268_log
#print axioms leaf01268_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
