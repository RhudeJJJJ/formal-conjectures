/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01107 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 571173122141022529343035801600000000000 671715764598402998917073167975440187392 3389670836952134452681428172800000000000))
theorem leaf01107_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 571173122141022529343035801600000000000 671715764598402998917073167975440187392 3389670836952134452681428172800000000000 raw01107=true := by decide +kernel
#print axioms leaf01107_raw
theorem leaf01107_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01107=true := by decide +kernel
#print axioms leaf01107_rectangular
def affine01107 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01107 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01107_transform : affine01107=(NestedInteger.clearedAll 3 raw01107 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/16),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01107_transform
theorem leaf01107_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01107=true := by decide +kernel
#print axioms leaf01107_sign
theorem leaf01107_log : RationalLog.accepts (263475873/268435456) (-20023905/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01107_log
def leaf01107 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (39633096953/200000000000) (263475873/268435456) (-20023905/2147483648) 1 8 ![60,0,4] ![(9/16),0,(3/4)] ![(1/32),1,(1/8)] affine01107
theorem leaf01107_checked : FastNestedCellData.accepts 1 2 4 leaf01107=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (39633096953/200000000000) (263475873/268435456) (-20023905/2147483648) 1 8 ![60,0,4] ![(9/16),0,(3/4)] ![(1/32),1,(1/8)] 571173122141022529343035801600000000000 671715764598402998917073167975440187392 3389670836952134452681428172800000000000 raw01107 affine01107
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01107_raw leaf01107_rectangular
    leaf01107_transform leaf01107_sign leaf01107_log
#print axioms leaf01107_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
