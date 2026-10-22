/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00499 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 905908072244830011392000000000000 905914982508695655122764327550976 72058143693023835119532638208000000000000))
theorem leaf00499_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 905908072244830011392000000000000 905914982508695655122764327550976 72058143693023835119532638208000000000000 raw00499=true := by decide +kernel
#print axioms leaf00499_raw
theorem leaf00499_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00499=true := by decide +kernel
#print axioms leaf00499_rectangular
def affine00499 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00499 (IntegerComputedClassCell.leftNumerator ![(1/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/512),0,0] ![(1/512),1,1]))
theorem leaf00499_transform : affine00499=(NestedInteger.clearedAll 3 raw00499 (IntegerComputedClassCell.leftNumerator ![(1/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf00499_transform
theorem leaf00499_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00499=true := by decide +kernel
#print axioms leaf00499_sign
theorem leaf00499_log : RationalLog.accepts (1073750001/1073741824) (16353/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00499_log
def leaf00499 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (3143/250000000000) (1073750001/1073741824) (16353/4294967296) 0 8 ![52,0,4] ![(1/512),0,0] ![(1/512),1,1] affine00499
theorem leaf00499_checked : FastNestedCellData.accepts 1 0 4 leaf00499=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (3143/250000000000) (1073750001/1073741824) (16353/4294967296) 0 8 ![52,0,4] ![(1/512),0,0] ![(1/512),1,1] 905908072244830011392000000000000 905914982508695655122764327550976 72058143693023835119532638208000000000000 raw00499 affine00499
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00499_raw leaf00499_rectangular
    leaf00499_transform leaf00499_sign leaf00499_log
#print axioms leaf00499_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
