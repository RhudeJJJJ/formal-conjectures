/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00128 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25374310152351050548488699904000000000000 24089934181081664210167885692476709666816 1094563871694427498236245704704000000000000))
theorem leaf00128_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25374310152351050548488699904000000000000 24089934181081664210167885692476709666816 1094563871694427498236245704704000000000000 raw00128=true := by decide +kernel
#print axioms leaf00128_raw
theorem leaf00128_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00128=true := by decide +kernel
#print axioms leaf00128_rectangular
def affine00128 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00128 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00128_transform : affine00128=(NestedInteger.clearedAll 3 raw00128 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00128_transform
theorem leaf00128_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00128=true := by decide +kernel
#print axioms leaf00128_sign
theorem leaf00128_log : RationalLog.accepts (1994879373/2147483648) (-158297877/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00128_log
def leaf00128 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11004352877/500000000000) (1994879373/2147483648) (-158297877/4294967296) 1 8 ![60,0,4] ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00128
theorem leaf00128_checked : FastNestedCellData.accepts 1 2 4 leaf00128=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11004352877/500000000000) (1994879373/2147483648) (-158297877/4294967296) 1 8 ![60,0,4] ![(91/32000),0,(1/4)] ![(3/32000),1,(1/4)] 25374310152351050548488699904000000000000 24089934181081664210167885692476709666816 1094563871694427498236245704704000000000000 raw00128 affine00128
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00128_raw leaf00128_rectangular
    leaf00128_transform leaf00128_sign leaf00128_log
#print axioms leaf00128_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
