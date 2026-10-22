/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01128 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 164101647149096398121942908928000000000000 203769843722621050264604684880640072482816 1431616555345952509924340662272000000000000))
theorem leaf01128_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 164101647149096398121942908928000000000000 203769843722621050264604684880640072482816 1431616555345952509924340662272000000000000 raw01128=true := by decide +kernel
#print axioms leaf01128_raw
theorem leaf01128_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01128=true := by decide +kernel
#print axioms leaf01128_rectangular
def affine01128 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01128 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01128_transform : affine01128=(NestedInteger.clearedAll 3 raw01128 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01128_transform
theorem leaf01128_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01128=true := by decide +kernel
#print axioms leaf01128_sign
theorem leaf01128_log : RationalLog.accepts (2334334927/2147483648) (44791281/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01128_log
def leaf01128 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71167744939/500000000000) (2334334927/2147483648) (44791281/1073741824) 0 8 ![60,0,4] ![(3/4),0,(7/8)] ![(1/16),1,(1/16)] affine01128
theorem leaf01128_checked : FastNestedCellData.accepts 1 2 4 leaf01128=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71167744939/500000000000) (2334334927/2147483648) (44791281/1073741824) 0 8 ![60,0,4] ![(3/4),0,(7/8)] ![(1/16),1,(1/16)] 164101647149096398121942908928000000000000 203769843722621050264604684880640072482816 1431616555345952509924340662272000000000000 raw01128 affine01128
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01128_raw leaf01128_rectangular
    leaf01128_transform leaf01128_sign leaf01128_log
#print axioms leaf01128_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
