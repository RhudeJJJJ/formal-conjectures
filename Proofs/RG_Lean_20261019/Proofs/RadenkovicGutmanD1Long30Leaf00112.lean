/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00112 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 748163703712597989966114455552000000000000 680502958149297410306031218691142053789696 16778498940927700159186933383168000000000000))
theorem leaf00112_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 748163703712597989966114455552000000000000 680502958149297410306031218691142053789696 16778498940927700159186933383168000000000000 raw00112=true := by decide +kernel
#print axioms leaf00112_raw
theorem leaf00112_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00112=true := by decide +kernel
#print axioms leaf00112_rectangular
def affine00112 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00112 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00112_transform : affine00112=(NestedInteger.clearedAll 3 raw00112 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00112_transform
theorem leaf00112_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00112=true := by decide +kernel
#print axioms leaf00112_sign
theorem leaf00112_log : RationalLog.accepts (3754282389/4294967296) (-144468525/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00112_log
def leaf00112 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40558035647/1000000000000) (3754282389/4294967296) (-144468525/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00112
theorem leaf00112_checked : FastNestedCellData.accepts 1 2 4 leaf00112=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40558035647/1000000000000) (3754282389/4294967296) (-144468525/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/8)] ![(3/32000),1,(1/8)] 748163703712597989966114455552000000000000 680502958149297410306031218691142053789696 16778498940927700159186933383168000000000000 raw00112 affine00112
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00112_raw leaf00112_rectangular
    leaf00112_transform leaf00112_sign leaf00112_log
#print axioms leaf00112_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
