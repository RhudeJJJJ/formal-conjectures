/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01345 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 829418242114823734006120448000000000000 832432600397059713387165839536473243648 18513785154982485506139164246016000000000000))
theorem leaf01345_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 829418242114823734006120448000000000000 832432600397059713387165839536473243648 18513785154982485506139164246016000000000000 raw01345=true := by decide +kernel
#print axioms leaf01345_raw
theorem leaf01345_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01345=true := by decide +kernel
#print axioms leaf01345_rectangular
def affine01345 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01345 (IntegerComputedClassCell.leftNumerator ![(11/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(11/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(11/256),0,0] ![(1/256),1,1]))
theorem leaf01345_transform : affine01345=(NestedInteger.clearedAll 3 raw01345 (IntegerComputedClassCell.leftNumerator ![(11/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(11/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(11/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01345_transform
theorem leaf01345_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01345=true := by decide +kernel
#print axioms leaf01345_sign
theorem leaf01345_log : RationalLog.accepts (4310382707/4294967296) (3846953/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01345_log
def leaf01345 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (44962853/1000000000000) (4310382707/4294967296) (3846953/2147483648) 0 8 ![60,0,4] ![(11/256),0,0] ![(1/256),1,1] affine01345
theorem leaf01345_checked : FastNestedCellData.accepts 1 2 4 leaf01345=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (44962853/1000000000000) (4310382707/4294967296) (3846953/2147483648) 0 8 ![60,0,4] ![(11/256),0,0] ![(1/256),1,1] 829418242114823734006120448000000000000 832432600397059713387165839536473243648 18513785154982485506139164246016000000000000 raw01345 affine01345
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01345_raw leaf01345_rectangular
    leaf01345_transform leaf01345_sign leaf01345_log
#print axioms leaf01345_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
