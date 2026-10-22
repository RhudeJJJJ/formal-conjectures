/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00096 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1087189438836657031562125115392000000000000 1410834553856970563972490869049730793472 5984537518409397341062692864000000000000))
theorem leaf00096_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1087189438836657031562125115392000000000000 1410834553856970563972490869049730793472 5984537518409397341062692864000000000000 raw00096=true := by decide +kernel
#print axioms leaf00096_raw
theorem leaf00096_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00096=true := by decide +kernel
#print axioms leaf00096_rectangular
def affine00096 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00096 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00096_transform : affine00096=(NestedInteger.clearedAll 3 raw00096 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00096_transform
theorem leaf00096_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00096=true := by decide +kernel
#print axioms leaf00096_sign
theorem leaf00096_log : RationalLog.accepts (4510257/4294967296) (-7364629007/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00096_log
def leaf00096 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (117873315149/500000000000) (4510257/4294967296) (-7364629007/2147483648) 10 8 ![52,0,4] ![(33/3200),0,0] ![(1/3200),1,(1/4)] affine00096
theorem leaf00096_checked : FastNestedCellData.accepts 1 0 4 leaf00096=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (117873315149/500000000000) (4510257/4294967296) (-7364629007/2147483648) 10 8 ![52,0,4] ![(33/3200),0,0] ![(1/3200),1,(1/4)] 1087189438836657031562125115392000000000000 1410834553856970563972490869049730793472 5984537518409397341062692864000000000000 raw00096 affine00096
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00096_raw leaf00096_rectangular
    leaf00096_transform leaf00096_sign leaf00096_log
#print axioms leaf00096_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
