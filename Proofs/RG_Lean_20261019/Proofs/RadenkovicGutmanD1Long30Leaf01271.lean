/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01271 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 287658936603145184251949875200000000000 303607216165751215504204323820494913536 111254066195314698586122983833600000000000))
theorem leaf01271_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 287658936603145184251949875200000000000 303607216165751215504204323820494913536 111254066195314698586122983833600000000000 raw01271=true := by decide +kernel
#print axioms leaf01271_raw
theorem leaf01271_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01271=true := by decide +kernel
#print axioms leaf01271_rectangular
def affine01271 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01271 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01271_transform : affine01271=(NestedInteger.clearedAll 3 raw01271 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01271_transform
theorem leaf01271_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01271=true := by decide +kernel
#print axioms leaf01271_sign
theorem leaf01271_log : RationalLog.accepts (4520750353/4294967296) (27506069/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01271_log
def leaf01271 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (545790777/200000000000) (4520750353/4294967296) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(1/2)] ![(1/128),1,(1/4)] affine01271
theorem leaf01271_checked : FastNestedCellData.accepts 1 2 4 leaf01271=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (545790777/200000000000) (4520750353/4294967296) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(1/2)] ![(1/128),1,(1/4)] 287658936603145184251949875200000000000 303607216165751215504204323820494913536 111254066195314698586122983833600000000000 raw01271 affine01271
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01271_raw leaf01271_rectangular
    leaf01271_transform leaf01271_sign leaf01271_log
#print axioms leaf01271_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
