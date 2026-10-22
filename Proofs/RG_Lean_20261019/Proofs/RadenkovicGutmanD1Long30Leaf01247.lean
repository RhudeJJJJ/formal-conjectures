/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01247 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 619117293835688616082276352000000000000 667159270287063137399016229585129832448 138042819164606919596557991936000000000000))
theorem leaf01247_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 619117293835688616082276352000000000000 667159270287063137399016229585129832448 138042819164606919596557991936000000000000 raw01247=true := by decide +kernel
#print axioms leaf01247_raw
theorem leaf01247_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01247=true := by decide +kernel
#print axioms leaf01247_rectangular
def affine01247 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01247 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01247_transform : affine01247=(NestedInteger.clearedAll 3 raw01247 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/32),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01247_transform
theorem leaf01247_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01247=true := by decide +kernel
#print axioms leaf01247_sign
theorem leaf01247_log : RationalLog.accepts (4605985503/4294967296) (150136407/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01247_log
def leaf01247 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1208246967/250000000000) (4605985503/4294967296) (150136407/4294967296) 0 8 ![60,0,4] ![(7/32),0,(3/4)] ![(1/64),1,(1/8)] affine01247
theorem leaf01247_checked : FastNestedCellData.accepts 1 2 4 leaf01247=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1208246967/250000000000) (4605985503/4294967296) (150136407/4294967296) 0 8 ![60,0,4] ![(7/32),0,(3/4)] ![(1/64),1,(1/8)] 619117293835688616082276352000000000000 667159270287063137399016229585129832448 138042819164606919596557991936000000000000 raw01247 affine01247
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01247_raw leaf01247_rectangular
    leaf01247_transform leaf01247_sign leaf01247_log
#print axioms leaf01247_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
