/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01138 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2178663000393112524682493427712000000000000 2759137017634471035402554583246159864659968 23361618763166942409070030618624000000000000))
theorem leaf01138_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2178663000393112524682493427712000000000000 2759137017634471035402554583246159864659968 23361618763166942409070030618624000000000000 raw01138=true := by decide +kernel
#print axioms leaf01138_raw
theorem leaf01138_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01138=true := by decide +kernel
#print axioms leaf01138_rectangular
def affine01138 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01138 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01138_transform : affine01138=(NestedInteger.clearedAll 3 raw01138 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01138_transform
theorem leaf01138_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01138=true := by decide +kernel
#print axioms leaf01138_sign
theorem leaf01138_log : RationalLog.accepts (4864747067/4294967296) (267513719/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01138_log
def leaf01138 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (118105557907/1000000000000) (4864747067/4294967296) (267513719/4294967296) 0 8 ![60,0,4] ![(7/8),0,(7/8)] ![(1/16),1,(1/16)] affine01138
theorem leaf01138_checked : FastNestedCellData.accepts 1 2 4 leaf01138=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (118105557907/1000000000000) (4864747067/4294967296) (267513719/4294967296) 0 8 ![60,0,4] ![(7/8),0,(7/8)] ![(1/16),1,(1/16)] 2178663000393112524682493427712000000000000 2759137017634471035402554583246159864659968 23361618763166942409070030618624000000000000 raw01138 affine01138
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01138_raw leaf01138_rectangular
    leaf01138_transform leaf01138_sign leaf01138_log
#print axioms leaf01138_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
