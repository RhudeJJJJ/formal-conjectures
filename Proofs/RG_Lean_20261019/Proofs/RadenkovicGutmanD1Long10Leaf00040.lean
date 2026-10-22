/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00040 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 38718736272465133800297332736000000000000 35632993062212182014969357351095774478336 1061037831550988487866319896576000000000000))
theorem leaf00040_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 38718736272465133800297332736000000000000 35632993062212182014969357351095774478336 1061037831550988487866319896576000000000000 raw00040=true := by decide +kernel
#print axioms leaf00040_raw
theorem leaf00040_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00040=true := by decide +kernel
#print axioms leaf00040_rectangular
def affine00040 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00040 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)]))
theorem leaf00040_transform : affine00040=(NestedInteger.clearedAll 3 raw00040 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00040_transform
theorem leaf00040_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00040=true := by decide +kernel
#print axioms leaf00040_sign
theorem leaf00040_log : RationalLog.accepts (1912121893/2147483648) (-124643401/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00040_log
def leaf00040 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (16791575193/500000000000) (1912121893/2147483648) (-124643401/2147483648) 1 8 ![52,0,4] ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)] affine00040
theorem leaf00040_checked : FastNestedCellData.accepts 1 0 4 leaf00040=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (16791575193/500000000000) (1912121893/2147483648) (-124643401/2147483648) 1 8 ![52,0,4] ![(17/4000),0,(1/4)] ![(3/8000),1,(1/4)] 38718736272465133800297332736000000000000 35632993062212182014969357351095774478336 1061037831550988487866319896576000000000000 raw00040 affine00040
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00040_raw leaf00040_rectangular
    leaf00040_transform leaf00040_sign leaf00040_log
#print axioms leaf00040_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
