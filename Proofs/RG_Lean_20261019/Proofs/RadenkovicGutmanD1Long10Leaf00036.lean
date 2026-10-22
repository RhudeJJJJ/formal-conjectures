/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00036 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5472685908890603776897345126400000000000 455985778951983213444099485168828416 4803087726034108989571072000000000000))
theorem leaf00036_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5472685908890603776897345126400000000000 455985778951983213444099485168828416 4803087726034108989571072000000000000 raw00036=true := by decide +kernel
#print axioms leaf00036_raw
theorem leaf00036_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00036=true := by decide +kernel
#print axioms leaf00036_rectangular
def affine00036 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00036 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,0] ![(3/8000),1,(1/4)]))
theorem leaf00036_transform : affine00036=(NestedInteger.clearedAll 3 raw00036 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,0] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00036_transform
theorem leaf00036_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00036=true := by decide +kernel
#print axioms leaf00036_sign
theorem leaf00036_log : RationalLog.accepts (163415/2147483648) (-20365692467/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00036_log
def leaf00036 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (23733991807/250000000000) (163415/2147483648) (-20365692467/4294967296) 14 8 ![52,0,4] ![(31/8000),0,0] ![(3/8000),1,(1/4)] affine00036
theorem leaf00036_checked : FastNestedCellData.accepts 1 0 4 leaf00036=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (23733991807/250000000000) (163415/2147483648) (-20365692467/4294967296) 14 8 ![52,0,4] ![(31/8000),0,0] ![(3/8000),1,(1/4)] 5472685908890603776897345126400000000000 455985778951983213444099485168828416 4803087726034108989571072000000000000 raw00036 affine00036
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00036_raw leaf00036_rectangular
    leaf00036_transform leaf00036_sign leaf00036_log
#print axioms leaf00036_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
