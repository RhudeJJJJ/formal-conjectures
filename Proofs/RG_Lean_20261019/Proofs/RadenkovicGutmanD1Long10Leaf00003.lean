/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00003 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9317746673081920993661812736000000000000 29177377456549539237495240457715712 902557965405614084456448000000000000))
theorem leaf00003_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9317746673081920993661812736000000000000 29177377456549539237495240457715712 902557965405614084456448000000000000 raw00003=true := by decide +kernel
#print axioms leaf00003_raw
theorem leaf00003_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00003=true := by decide +kernel
#print axioms leaf00003_rectangular
def affine00003 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00003 (IntegerComputedClassCell.leftNumerator ![(1/800),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,0] ![(1/4000),1,(1/4)]))
theorem leaf00003_transform : affine00003=(NestedInteger.clearedAll 3 raw00003 (IntegerComputedClassCell.leftNumerator ![(1/800),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,0] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00003_transform
theorem leaf00003_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00003=true := by decide +kernel
#print axioms leaf00003_sign
theorem leaf00003_log : RationalLog.accepts (3257/1073741824) (-27285613535/4294967296) 19 8=true := by decide +kernel
#print axioms leaf00003_log
def leaf00003 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (16163713897/500000000000) (3257/1073741824) (-27285613535/4294967296) 19 8 ![52,0,4] ![(1/800),0,0] ![(1/4000),1,(1/4)] affine00003
theorem leaf00003_checked : FastNestedCellData.accepts 1 0 4 leaf00003=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (16163713897/500000000000) (3257/1073741824) (-27285613535/4294967296) 19 8 ![52,0,4] ![(1/800),0,0] ![(1/4000),1,(1/4)] 9317746673081920993661812736000000000000 29177377456549539237495240457715712 902557965405614084456448000000000000 raw00003 affine00003
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00003_raw leaf00003_rectangular
    leaf00003_transform leaf00003_sign leaf00003_log
#print axioms leaf00003_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
