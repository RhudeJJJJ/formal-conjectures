/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00091 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 51807531254094567393245727293440000000000 44001839238252263980983518723527269154816 626697043886953427895630954496000000000000))
theorem leaf00091_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 51807531254094567393245727293440000000000 44001839238252263980983518723527269154816 626697043886953427895630954496000000000000 raw00091=true := by decide +kernel
#print axioms leaf00091_raw
theorem leaf00091_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00091=true := by decide +kernel
#print axioms leaf00091_rectangular
def affine00091 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00091 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00091_transform : affine00091=(NestedInteger.clearedAll 3 raw00091 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00091_transform
theorem leaf00091_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00091=true := by decide +kernel
#print axioms leaf00091_sign
theorem leaf00091_log : RationalLog.accepts (3408535775/4294967296) (-248207395/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00091_log
def leaf00091 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (70212297421/1000000000000) (3408535775/4294967296) (-248207395/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)] affine00091
theorem leaf00091_checked : FastNestedCellData.accepts 1 2 4 leaf00091=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (70212297421/1000000000000) (3408535775/4294967296) (-248207395/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/16)] ![(3/32000),1,(1/16)] 51807531254094567393245727293440000000000 44001839238252263980983518723527269154816 626697043886953427895630954496000000000000 raw00091 affine00091
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00091_raw leaf00091_rectangular
    leaf00091_transform leaf00091_sign leaf00091_log
#print axioms leaf00091_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
