/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00545 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 184249052636140880174773383987200000000000 1741551862846347939023413627269804982272 2179520128148349338467172352000000000000))
theorem leaf00545_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 184249052636140880174773383987200000000000 1741551862846347939023413627269804982272 2179520128148349338467172352000000000000 raw00545=true := by decide +kernel
#print axioms leaf00545_raw
theorem leaf00545_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00545=true := by decide +kernel
#print axioms leaf00545_rectangular
def affine00545 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00545 (IntegerComputedClassCell.leftNumerator ![(13/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/800),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00545_transform : affine00545=(NestedInteger.clearedAll 3 raw00545 (IntegerComputedClassCell.leftNumerator ![(13/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/800),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00545_transform
theorem leaf00545_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00545=true := by decide +kernel
#print axioms leaf00545_sign
theorem leaf00545_log : RationalLog.accepts (11282805/2147483648) (-11271652655/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00545_log
def leaf00545 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (399526446293/500000000000) (11282805/2147483648) (-11271652655/4294967296) 8 8 ![60,0,4] ![(13/800),0,0] ![(1/3200),1,(1/16)] affine00545
theorem leaf00545_checked : FastNestedCellData.accepts 1 2 4 leaf00545=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (399526446293/500000000000) (11282805/2147483648) (-11271652655/4294967296) 8 8 ![60,0,4] ![(13/800),0,0] ![(1/3200),1,(1/16)] 184249052636140880174773383987200000000000 1741551862846347939023413627269804982272 2179520128148349338467172352000000000000 raw00545 affine00545
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00545_raw leaf00545_rectangular
    leaf00545_transform leaf00545_sign leaf00545_log
#print axioms leaf00545_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
