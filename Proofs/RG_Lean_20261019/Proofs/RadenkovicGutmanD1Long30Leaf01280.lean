/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01280 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 98255177819637014621637836800000000000 102895825629453182680683591919743270912 48294985662837484462720784793600000000000))
theorem leaf01280_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 98255177819637014621637836800000000000 102895825629453182680683591919743270912 48294985662837484462720784793600000000000 raw01280=true := by decide +kernel
#print axioms leaf01280_raw
theorem leaf01280_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01280=true := by decide +kernel
#print axioms leaf01280_rectangular
def affine01280 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01280 (IntegerComputedClassCell.leftNumerator ![(21/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01280_transform : affine01280=(NestedInteger.clearedAll 3 raw01280 (IntegerComputedClassCell.leftNumerator ![(21/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01280_transform
theorem leaf01280_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01280=true := by decide +kernel
#print axioms leaf01280_sign
theorem leaf01280_log : RationalLog.accepts (1122064623/1073741824) (94533995/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01280_log
def leaf01280 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (426113909/200000000000) (1122064623/1073741824) (94533995/4294967296) 0 8 ![60,0,4] ![(21/128),0,0] ![(1/128),1,(1/2)] affine01280
theorem leaf01280_checked : FastNestedCellData.accepts 1 2 4 leaf01280=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (426113909/200000000000) (1122064623/1073741824) (94533995/4294967296) 0 8 ![60,0,4] ![(21/128),0,0] ![(1/128),1,(1/2)] 98255177819637014621637836800000000000 102895825629453182680683591919743270912 48294985662837484462720784793600000000000 raw01280 affine01280
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01280_raw leaf01280_rectangular
    leaf01280_transform leaf01280_sign leaf01280_log
#print axioms leaf01280_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
