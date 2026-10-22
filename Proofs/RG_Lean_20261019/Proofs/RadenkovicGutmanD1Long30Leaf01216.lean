/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01216 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 527469423224868231698186240000000000 597841736466488686850984634237321216 51044472021066910336548864000000000000))
theorem leaf01216_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 527469423224868231698186240000000000 597841736466488686850984634237321216 51044472021066910336548864000000000000 raw01216=true := by decide +kernel
#print axioms leaf01216_raw
theorem leaf01216_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01216=true := by decide +kernel
#print axioms leaf01216_rectangular
def affine01216 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01216 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01216_transform : affine01216=(NestedInteger.clearedAll 3 raw01216 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01216_transform
theorem leaf01216_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01216=true := by decide +kernel
#print axioms leaf01216_sign
theorem leaf01216_log : RationalLog.accepts (37590825/33554432) (243934919/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01216_log
def leaf01216 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (11712173969/1000000000000) (37590825/33554432) (243934919/4294967296) 0 8 ![60,0,4] ![(5/16),0,(1/2)] ![(1/64),1,(1/4)] affine01216
theorem leaf01216_checked : FastNestedCellData.accepts 1 2 4 leaf01216=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (11712173969/1000000000000) (37590825/33554432) (243934919/4294967296) 0 8 ![60,0,4] ![(5/16),0,(1/2)] ![(1/64),1,(1/4)] 527469423224868231698186240000000000 597841736466488686850984634237321216 51044472021066910336548864000000000000 raw01216 affine01216
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01216_raw leaf01216_rectangular
    leaf01216_transform leaf01216_sign leaf01216_log
#print axioms leaf01216_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
