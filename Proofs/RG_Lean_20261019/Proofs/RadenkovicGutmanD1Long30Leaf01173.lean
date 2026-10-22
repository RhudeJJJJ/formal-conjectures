/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01173 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 818092914891165023777740292096000000000000 1022874155888113097418899852148673999798272 23064247874325995367197847846912000000000000))
theorem leaf01173_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 818092914891165023777740292096000000000000 1022874155888113097418899852148673999798272 23064247874325995367197847846912000000000000 raw01173=true := by decide +kernel
#print axioms leaf01173_raw
theorem leaf01173_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01173=true := by decide +kernel
#print axioms leaf01173_rectangular
def affine01173 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01173 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01173_transform : affine01173=(NestedInteger.clearedAll 3 raw01173 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01173_transform
theorem leaf01173_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01173=true := by decide +kernel
#print axioms leaf01173_sign
theorem leaf01173_log : RationalLog.accepts (5142020687/4294967296) (386551761/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01173_log
def leaf01173 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (44348905781/1000000000000) (5142020687/4294967296) (386551761/4294967296) 0 8 ![60,0,4] ![(9/16),0,(7/8)] ![(1/16),1,(1/16)] affine01173
theorem leaf01173_checked : FastNestedCellData.accepts 1 2 4 leaf01173=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (44348905781/1000000000000) (5142020687/4294967296) (386551761/4294967296) 0 8 ![60,0,4] ![(9/16),0,(7/8)] ![(1/16),1,(1/16)] 818092914891165023777740292096000000000000 1022874155888113097418899852148673999798272 23064247874325995367197847846912000000000000 raw01173 affine01173
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01173_raw leaf01173_rectangular
    leaf01173_transform leaf01173_sign leaf01173_log
#print axioms leaf01173_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
