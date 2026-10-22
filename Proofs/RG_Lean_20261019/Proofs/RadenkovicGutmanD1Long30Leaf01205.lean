/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01205 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 90006345953254113155278176256000000000000 103636080339533066438263909974522772586496 7080049858627591280536166858752000000000000))
theorem leaf01205_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 90006345953254113155278176256000000000000 103636080339533066438263909974522772586496 7080049858627591280536166858752000000000000 raw01205=true := by decide +kernel
#print axioms leaf01205_raw
theorem leaf01205_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01205=true := by decide +kernel
#print axioms leaf01205_rectangular
def affine01205 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01205 (IntegerComputedClassCell.leftNumerator ![(11/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/32),0,0] ![(1/64),1,(1/2)]))
theorem leaf01205_transform : affine01205=(NestedInteger.clearedAll 3 raw01205 (IntegerComputedClassCell.leftNumerator ![(11/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/32),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01205_transform
theorem leaf01205_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01205=true := by decide +kernel
#print axioms leaf01205_sign
theorem leaf01205_log : RationalLog.accepts (4874013057/4294967296) (271600187/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01205_log
def leaf01205 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (14637761373/1000000000000) (4874013057/4294967296) (271600187/4294967296) 0 8 ![60,0,4] ![(11/32),0,0] ![(1/64),1,(1/2)] affine01205
theorem leaf01205_checked : FastNestedCellData.accepts 1 2 4 leaf01205=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (14637761373/1000000000000) (4874013057/4294967296) (271600187/4294967296) 0 8 ![60,0,4] ![(11/32),0,0] ![(1/64),1,(1/2)] 90006345953254113155278176256000000000000 103636080339533066438263909974522772586496 7080049858627591280536166858752000000000000 raw01205 affine01205
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01205_raw leaf01205_rectangular
    leaf01205_transform leaf01205_sign leaf01205_log
#print axioms leaf01205_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
