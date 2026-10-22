/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00011 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 125761340163541299125788082176000000000000 123485228966942802770145189032256723746816 18112882803844288070101401337856000000000000))
theorem leaf00011_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 125761340163541299125788082176000000000000 123485228966942802770145189032256723746816 18112882803844288070101401337856000000000000 raw00011=true := by decide +kernel
#print axioms leaf00011_raw
theorem leaf00011_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00011=true := by decide +kernel
#print axioms leaf00011_rectangular
def affine00011 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00011 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)]))
theorem leaf00011_transform : affine00011=(NestedInteger.clearedAll 3 raw00011 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)])) := by decide +kernel
#print axioms leaf00011_transform
theorem leaf00011_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00011=true := by decide +kernel
#print axioms leaf00011_sign
theorem leaf00011_log : RationalLog.accepts (4188677701/4294967296) (-53813489/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00011_log
def leaf00011 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6817535911/1000000000000) (4188677701/4294967296) (-53813489/4294967296) 1 8 ![52,0,4] ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)] affine00011
theorem leaf00011_checked : FastNestedCellData.accepts 1 0 4 leaf00011=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6817535911/1000000000000) (4188677701/4294967296) (-53813489/4294967296) 1 8 ![52,0,4] ![(7/4000),0,(1/2)] ![(1/4000),1,(1/2)] 125761340163541299125788082176000000000000 123485228966942802770145189032256723746816 18112882803844288070101401337856000000000000 raw00011 affine00011
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00011_raw leaf00011_rectangular
    leaf00011_transform leaf00011_sign leaf00011_log
#print axioms leaf00011_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
