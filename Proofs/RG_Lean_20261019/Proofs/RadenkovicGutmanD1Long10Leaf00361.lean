/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00361 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2102718320679928440358436864000000000000 1627447747643100295723223054182376275968 3485665672747083060165476352000000000000))
theorem leaf00361_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2102718320679928440358436864000000000000 1627447747643100295723223054182376275968 3485665672747083060165476352000000000000 raw00361=true := by decide +kernel
#print axioms leaf00361_raw
theorem leaf00361_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00361=true := by decide +kernel
#print axioms leaf00361_rectangular
def affine00361 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00361 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf00361_transform : affine00361=(NestedInteger.clearedAll 3 raw00361 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00361_transform
theorem leaf00361_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00361=true := by decide +kernel
#print axioms leaf00361_sign
theorem leaf00361_log : RationalLog.accepts (1133068389/2147483648) (-686515557/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00361_log
def leaf00361 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (14590539337/31250000000) (1133068389/2147483648) (-686515557/2147483648) 1 8 ![52,0,4] ![(7/32),0,(1/4)] ![(3/160),1,(1/4)] affine00361
theorem leaf00361_checked : FastNestedCellData.accepts 1 0 4 leaf00361=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (14590539337/31250000000) (1133068389/2147483648) (-686515557/2147483648) 1 8 ![52,0,4] ![(7/32),0,(1/4)] ![(3/160),1,(1/4)] 2102718320679928440358436864000000000000 1627447747643100295723223054182376275968 3485665672747083060165476352000000000000 raw00361 affine00361
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00361_raw leaf00361_rectangular
    leaf00361_transform leaf00361_sign leaf00361_log
#print axioms leaf00361_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
