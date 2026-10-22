/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00074 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 13340587638596877436615393280000000000 12446950142589255562358392984046665728 430276592753443056609436631040000000000))
theorem leaf00074_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 13340587638596877436615393280000000000 12446950142589255562358392984046665728 430276592753443056609436631040000000000 raw00074=true := by decide +kernel
#print axioms leaf00074_raw
theorem leaf00074_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00074=true := by decide +kernel
#print axioms leaf00074_rectangular
def affine00074 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00074 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00074_transform : affine00074=(NestedInteger.clearedAll 3 raw00074 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00074_transform
theorem leaf00074_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00074=true := by decide +kernel
#print axioms leaf00074_sign
theorem leaf00074_log : RationalLog.accepts (3894600853/4294967296) (-210137203/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00074_log
def leaf00074 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (144638941/5000000000) (3894600853/4294967296) (-210137203/4294967296) 1 8 ![52,0,4] ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)] affine00074
theorem leaf00074_checked : FastNestedCellData.accepts 1 0 4 leaf00074=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (144638941/5000000000) (3894600853/4294967296) (-210137203/4294967296) 1 8 ![52,0,4] ![(1/128),0,(1/2)] ![(1/3200),1,(1/2)] 13340587638596877436615393280000000000 12446950142589255562358392984046665728 430276592753443056609436631040000000000 raw00074 affine00074
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00074_raw leaf00074_rectangular
    leaf00074_transform leaf00074_sign leaf00074_log
#print axioms leaf00074_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
