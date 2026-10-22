/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00189 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17085498915791615402845405184000000000000 16497456251227639398735308528273282039808 1113240659643315124489118810112000000000000))
theorem leaf00189_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17085498915791615402845405184000000000000 16497456251227639398735308528273282039808 1113240659643315124489118810112000000000000 raw00189=true := by decide +kernel
#print axioms leaf00189_raw
theorem leaf00189_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00189=true := by decide +kernel
#print axioms leaf00189_rectangular
def affine00189 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00189 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00189_transform : affine00189=(NestedInteger.clearedAll 3 raw00189 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00189_transform
theorem leaf00189_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00189=true := by decide +kernel
#print axioms leaf00189_sign
theorem leaf00189_log : RationalLog.accepts (2043292139/2147483648) (-106803975/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00189_log
def leaf00189 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7409654017/500000000000) (2043292139/2147483648) (-106803975/4294967296) 1 8 ![60,0,4] ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00189
theorem leaf00189_checked : FastNestedCellData.accepts 1 2 4 leaf00189=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7409654017/500000000000) (2043292139/2147483648) (-106803975/4294967296) 1 8 ![60,0,4] ![(127/32000),0,(1/2)] ![(3/32000),1,(1/2)] 17085498915791615402845405184000000000000 16497456251227639398735308528273282039808 1113240659643315124489118810112000000000000 raw00189 affine00189
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00189_raw leaf00189_rectangular
    leaf00189_transform leaf00189_sign leaf00189_log
#print axioms leaf00189_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
