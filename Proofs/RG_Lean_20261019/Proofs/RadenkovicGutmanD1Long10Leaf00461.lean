/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00461 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 2356863857911301202071519232000000000000 2461553150622778901638669480307114115072 1204133006053565620860900868096000000000000))
theorem leaf00461_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 2356863857911301202071519232000000000000 2461553150622778901638669480307114115072 1204133006053565620860900868096000000000000 raw00461=true := by decide +kernel
#print axioms leaf00461_raw
theorem leaf00461_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00461=true := by decide +kernel
#print axioms leaf00461_rectangular
def affine00461 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00461 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00461_transform : affine00461=(NestedInteger.clearedAll 3 raw00461 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00461_transform
theorem leaf00461_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00461=true := by decide +kernel
#print axioms leaf00461_sign
theorem leaf00461_log : RationalLog.accepts (4476593713/4294967296) (88945517/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00461_log
def leaf00461 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (511063383/250000000000) (4476593713/4294967296) (88945517/4294967296) 0 8 ![52,0,4] ![(5/32),0,(3/4)] ![(1/64),1,(1/4)] affine00461
theorem leaf00461_checked : FastNestedCellData.accepts 1 0 4 leaf00461=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (511063383/250000000000) (4476593713/4294967296) (88945517/4294967296) 0 8 ![52,0,4] ![(5/32),0,(3/4)] ![(1/64),1,(1/4)] 2356863857911301202071519232000000000000 2461553150622778901638669480307114115072 1204133006053565620860900868096000000000000 raw00461 affine00461
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00461_raw leaf00461_rectangular
    leaf00461_transform leaf00461_sign leaf00461_log
#print axioms leaf00461_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
