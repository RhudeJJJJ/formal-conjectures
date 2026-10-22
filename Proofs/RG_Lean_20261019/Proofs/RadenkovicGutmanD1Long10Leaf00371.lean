/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00371 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 104348065979260509438424907776000000000000 94276126247968154852950862918783565037568 260409649911277603519874465792000000000000))
theorem leaf00371_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 104348065979260509438424907776000000000000 94276126247968154852950862918783565037568 260409649911277603519874465792000000000000 raw00371=true := by decide +kernel
#print axioms leaf00371_raw
theorem leaf00371_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00371=true := by decide +kernel
#print axioms leaf00371_rectangular
def affine00371 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00371 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf00371_transform : affine00371=(NestedInteger.clearedAll 3 raw00371 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00371_transform
theorem leaf00371_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00371=true := by decide +kernel
#print axioms leaf00371_sign
theorem leaf00371_log : RationalLog.accepts (712246783/1073741824) (-881499987/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00371_log
def leaf00371 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (181015039727/500000000000) (712246783/1073741824) (-881499987/4294967296) 1 8 ![52,0,4] ![(11/40),0,(1/2)] ![(3/80),1,(1/2)] affine00371
theorem leaf00371_checked : FastNestedCellData.accepts 1 0 4 leaf00371=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (181015039727/500000000000) (712246783/1073741824) (-881499987/4294967296) 1 8 ![52,0,4] ![(11/40),0,(1/2)] ![(3/80),1,(1/2)] 104348065979260509438424907776000000000000 94276126247968154852950862918783565037568 260409649911277603519874465792000000000000 raw00371 affine00371
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00371_raw leaf00371_rectangular
    leaf00371_transform leaf00371_sign leaf00371_log
#print axioms leaf00371_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
