/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01028 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8013531506086481923905048018944000000000000 6008509517989088571826202361812131673800704 13831284903367359145031296352256000000000000))
theorem leaf01028_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8013531506086481923905048018944000000000000 6008509517989088571826202361812131673800704 13831284903367359145031296352256000000000000 raw01028=true := by decide +kernel
#print axioms leaf01028_raw
theorem leaf01028_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01028=true := by decide +kernel
#print axioms leaf01028_rectangular
def affine01028 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01028 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)]))
theorem leaf01028_transform : affine01028=(NestedInteger.clearedAll 3 raw01028 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/4)] ![(3/320),1,(1/4)])) := by decide +kernel
#print axioms leaf01028_transform
theorem leaf01028_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01028=true := by decide +kernel
#print axioms leaf01028_sign
theorem leaf01028_log : RationalLog.accepts (2245060379/4294967296) (-1393097429/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01028_log
def leaf01028 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (434414413409/1000000000000) (2245060379/4294967296) (-1393097429/4294967296) 1 8 ![60,0,4] ![(1/5),0,(1/4)] ![(3/320),1,(1/4)] affine01028
theorem leaf01028_checked : FastNestedCellData.accepts 1 2 4 leaf01028=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (434414413409/1000000000000) (2245060379/4294967296) (-1393097429/4294967296) 1 8 ![60,0,4] ![(1/5),0,(1/4)] ![(3/320),1,(1/4)] 8013531506086481923905048018944000000000000 6008509517989088571826202361812131673800704 13831284903367359145031296352256000000000000 raw01028 affine01028
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01028_raw leaf01028_rectangular
    leaf01028_transform leaf01028_sign leaf01028_log
#print axioms leaf01028_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
