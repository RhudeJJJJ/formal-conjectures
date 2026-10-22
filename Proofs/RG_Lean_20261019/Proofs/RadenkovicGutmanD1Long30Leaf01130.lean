/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01130 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 604943450806236968421976702976000000000000 762306938538519031215157119591090311135232 5811320455693789144458542972928000000000000))
theorem leaf01130_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 604943450806236968421976702976000000000000 762306938538519031215157119591090311135232 5811320455693789144458542972928000000000000 raw01130=true := by decide +kernel
#print axioms leaf01130_raw
theorem leaf01130_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01130=true := by decide +kernel
#print axioms leaf01130_rectangular
def affine01130 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01130 (IntegerComputedClassCell.leftNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01130_transform : affine01130=(NestedInteger.clearedAll 3 raw01130 (IntegerComputedClassCell.leftNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01130_transform
theorem leaf01130_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01130=true := by decide +kernel
#print axioms leaf01130_sign
theorem leaf01130_log : RationalLog.accepts (2392294819/2147483648) (3622413/67108864) 0 8=true := by decide +kernel
#print axioms leaf01130_log
def leaf01130 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (131176200719/1000000000000) (2392294819/2147483648) (3622413/67108864) 0 8 ![60,0,4] ![(13/16),0,0] ![(1/16),1,(1/2)] affine01130
theorem leaf01130_checked : FastNestedCellData.accepts 1 2 4 leaf01130=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (131176200719/1000000000000) (2392294819/2147483648) (3622413/67108864) 0 8 ![60,0,4] ![(13/16),0,0] ![(1/16),1,(1/2)] 604943450806236968421976702976000000000000 762306938538519031215157119591090311135232 5811320455693789144458542972928000000000000 raw01130 affine01130
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01130_raw leaf01130_rectangular
    leaf01130_transform leaf01130_sign leaf01130_log
#print axioms leaf01130_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
