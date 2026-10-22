/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01242 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 103869585841939131916091392000000000000 112884327987795637856848368677056151552 19577850949956739647672418304000000000000))
theorem leaf01242_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 103869585841939131916091392000000000000 112884327987795637856848368677056151552 19577850949956739647672418304000000000000 raw01242=true := by decide +kernel
#print axioms leaf01242_raw
theorem leaf01242_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01242=true := by decide +kernel
#print axioms leaf01242_rectangular
def affine01242 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01242 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01242_transform : affine01242=(NestedInteger.clearedAll 3 raw01242 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/64),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01242_transform
theorem leaf01242_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01242=true := by decide +kernel
#print axioms leaf01242_sign
theorem leaf01242_log : RationalLog.accepts (4640963977/4294967296) (166383075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01242_log
def leaf01242 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (180185009/31250000000) (4640963977/4294967296) (166383075/4294967296) 0 8 ![60,0,4] ![(15/64),0,(3/4)] ![(1/64),1,(1/8)] affine01242
theorem leaf01242_checked : FastNestedCellData.accepts 1 2 4 leaf01242=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (180185009/31250000000) (4640963977/4294967296) (166383075/4294967296) 0 8 ![60,0,4] ![(15/64),0,(3/4)] ![(1/64),1,(1/8)] 103869585841939131916091392000000000000 112884327987795637856848368677056151552 19577850949956739647672418304000000000000 raw01242 affine01242
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01242_raw leaf01242_rectangular
    leaf01242_transform leaf01242_sign leaf01242_log
#print axioms leaf01242_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
