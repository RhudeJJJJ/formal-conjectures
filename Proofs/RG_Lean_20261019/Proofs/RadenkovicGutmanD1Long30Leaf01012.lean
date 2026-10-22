/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01012 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9963150060082010672404891697152000000000000 6233446773114940464001721972925079568252928 11541209017963486707863229825024000000000000))
theorem leaf01012_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9963150060082010672404891697152000000000000 6233446773114940464001721972925079568252928 11541209017963486707863229825024000000000000 raw01012=true := by decide +kernel
#print axioms leaf01012_raw
theorem leaf01012_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01012=true := by decide +kernel
#print axioms leaf01012_rectangular
def affine01012 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01012 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)]))
theorem leaf01012_transform : affine01012=(NestedInteger.clearedAll 3 raw01012 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/8)] ![(1/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01012_transform
theorem leaf01012_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01012=true := by decide +kernel
#print axioms leaf01012_sign
theorem leaf01012_log : RationalLog.accepts (1744783527/4294967296) (-1934482217/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01012_log
def leaf01012 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (540103446997/1000000000000) (1744783527/4294967296) (-1934482217/4294967296) 2 8 ![60,0,4] ![(13/80),0,(1/8)] ![(1/80),1,(1/8)] affine01012
theorem leaf01012_checked : FastNestedCellData.accepts 1 2 4 leaf01012=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (540103446997/1000000000000) (1744783527/4294967296) (-1934482217/4294967296) 2 8 ![60,0,4] ![(13/80),0,(1/8)] ![(1/80),1,(1/8)] 9963150060082010672404891697152000000000000 6233446773114940464001721972925079568252928 11541209017963486707863229825024000000000000 raw01012 affine01012
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01012_raw leaf01012_rectangular
    leaf01012_transform leaf01012_sign leaf01012_log
#print axioms leaf01012_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
