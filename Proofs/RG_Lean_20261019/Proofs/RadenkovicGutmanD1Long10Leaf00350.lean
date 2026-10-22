/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00350 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6545741352295975246943485952000000000000 4643164354630815658184906515494111019008 12778355961162818445782286336000000000000))
theorem leaf00350_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6545741352295975246943485952000000000000 4643164354630815658184906515494111019008 12778355961162818445782286336000000000000 raw00350=true := by decide +kernel
#print axioms leaf00350_raw
theorem leaf00350_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00350=true := by decide +kernel
#print axioms leaf00350_rectangular
def affine00350 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00350 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf00350_transform : affine00350=(NestedInteger.clearedAll 3 raw00350 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00350_transform
theorem leaf00350_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00350=true := by decide +kernel
#print axioms leaf00350_sign
theorem leaf00350_log : RationalLog.accepts (1117310839/2147483648) (-1403105719/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00350_log
def leaf00350 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (22710102383/62500000000) (1117310839/2147483648) (-1403105719/4294967296) 1 8 ![52,0,4] ![(13/80),0,(1/2)] ![(1/80),1,(1/2)] affine00350
theorem leaf00350_checked : FastNestedCellData.accepts 1 0 4 leaf00350=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (22710102383/62500000000) (1117310839/2147483648) (-1403105719/4294967296) 1 8 ![52,0,4] ![(13/80),0,(1/2)] ![(1/80),1,(1/2)] 6545741352295975246943485952000000000000 4643164354630815658184906515494111019008 12778355961162818445782286336000000000000 raw00350 affine00350
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00350_raw leaf00350_rectangular
    leaf00350_transform leaf00350_sign leaf00350_log
#print axioms leaf00350_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
