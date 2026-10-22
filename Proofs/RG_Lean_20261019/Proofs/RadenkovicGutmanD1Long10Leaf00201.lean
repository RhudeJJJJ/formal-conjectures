/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00201 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 162519326977027256998288162816000000000000 4066208557074738248417999816771623714816 7211479666554540471032479744000000000000))
theorem leaf00201_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 162519326977027256998288162816000000000000 4066208557074738248417999816771623714816 7211479666554540471032479744000000000000 raw00201=true := by decide +kernel
#print axioms leaf00201_raw
theorem leaf00201_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00201=true := by decide +kernel
#print axioms leaf00201_rectangular
def affine00201 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00201 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00201_transform : affine00201=(NestedInteger.clearedAll 3 raw00201 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00201_transform
theorem leaf00201_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00201=true := by decide +kernel
#print axioms leaf00201_sign
theorem leaf00201_log : RationalLog.accepts (17178641/1073741824) (-8880356303/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00201_log
def leaf00201 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (281926091807/500000000000) (17178641/1073741824) (-8880356303/4294967296) 6 8 ![52,0,4] ![(53/1600),0,0] ![(3/3200),1,(1/4)] affine00201
theorem leaf00201_checked : FastNestedCellData.accepts 1 0 4 leaf00201=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (281926091807/500000000000) (17178641/1073741824) (-8880356303/4294967296) 6 8 ![52,0,4] ![(53/1600),0,0] ![(3/3200),1,(1/4)] 162519326977027256998288162816000000000000 4066208557074738248417999816771623714816 7211479666554540471032479744000000000000 raw00201 affine00201
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00201_raw leaf00201_rectangular
    leaf00201_transform leaf00201_sign leaf00201_log
#print axioms leaf00201_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
