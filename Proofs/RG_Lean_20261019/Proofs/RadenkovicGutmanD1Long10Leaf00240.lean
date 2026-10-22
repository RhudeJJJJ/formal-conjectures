/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00240 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 738411206908187308930497511424000000000000 36979573651851306790604188036662420307968 57738215909435979665435000832000000000000))
theorem leaf00240_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 738411206908187308930497511424000000000000 36979573651851306790604188036662420307968 57738215909435979665435000832000000000000 raw00240=true := by decide +kernel
#print axioms leaf00240_raw
theorem leaf00240_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00240=true := by decide +kernel
#print axioms leaf00240_rectangular
def affine00240 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00240 (IntegerComputedClassCell.leftNumerator ![(29/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00240_transform : affine00240=(NestedInteger.clearedAll 3 raw00240 (IntegerComputedClassCell.leftNumerator ![(29/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00240_transform
theorem leaf00240_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00240=true := by decide +kernel
#print axioms leaf00240_sign
theorem leaf00240_log : RationalLog.accepts (65557939/2147483648) (-7492823469/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00240_log
def leaf00240 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (320234813887/500000000000) (65557939/2147483648) (-7492823469/4294967296) 6 8 ![52,0,4] ![(29/640),0,0] ![(3/3200),1,(1/4)] affine00240
theorem leaf00240_checked : FastNestedCellData.accepts 1 0 4 leaf00240=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (320234813887/500000000000) (65557939/2147483648) (-7492823469/4294967296) 6 8 ![52,0,4] ![(29/640),0,0] ![(3/3200),1,(1/4)] 738411206908187308930497511424000000000000 36979573651851306790604188036662420307968 57738215909435979665435000832000000000000 raw00240 affine00240
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00240_raw leaf00240_rectangular
    leaf00240_transform leaf00240_sign leaf00240_log
#print axioms leaf00240_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
