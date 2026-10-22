/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00192 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14349687403914980479100518400000000000 12400912363106568228780200944493133824 194599166955734097962467328000000000000))
theorem leaf00192_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14349687403914980479100518400000000000 12400912363106568228780200944493133824 194599166955734097962467328000000000000 raw00192=true := by decide +kernel
#print axioms leaf00192_raw
theorem leaf00192_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00192=true := by decide +kernel
#print axioms leaf00192_rectangular
def affine00192 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00192 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00192_transform : affine00192=(NestedInteger.clearedAll 3 raw00192 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00192_transform
theorem leaf00192_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00192=true := by decide +kernel
#print axioms leaf00192_sign
theorem leaf00192_log : RationalLog.accepts (872331455/1073741824) (-446108407/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00192_log
def leaf00192 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1991419169/31250000000) (872331455/1073741824) (-446108407/4294967296) 1 8 ![60,0,4] ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)] affine00192
theorem leaf00192_checked : FastNestedCellData.accepts 1 2 4 leaf00192=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1991419169/31250000000) (872331455/1073741824) (-446108407/4294967296) 1 8 ![60,0,4] ![(13/3200),0,(1/8)] ![(3/32000),1,(1/8)] 14349687403914980479100518400000000000 12400912363106568228780200944493133824 194599166955734097962467328000000000000 raw00192 affine00192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00192_raw leaf00192_rectangular
    leaf00192_transform leaf00192_sign leaf00192_log
#print axioms leaf00192_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
