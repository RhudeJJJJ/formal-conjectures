/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01261 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 15752067966113889280849870848000000000000 16760418907861047986032108884812730728448 4906897920110839529111189192704000000000000))
theorem leaf01261_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 15752067966113889280849870848000000000000 16760418907861047986032108884812730728448 4906897920110839529111189192704000000000000 raw01261=true := by decide +kernel
#print axioms leaf01261_raw
theorem leaf01261_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01261=true := by decide +kernel
#print axioms leaf01261_rectangular
def affine01261 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01261 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01261_transform : affine01261=(NestedInteger.clearedAll 3 raw01261 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(25/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01261_transform
theorem leaf01261_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01261=true := by decide +kernel
#print axioms leaf01261_sign
theorem leaf01261_log : RationalLog.accepts (4554348583/4294967296) (62962683/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01261_log
def leaf01261 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1707842631/500000000000) (4554348583/4294967296) (62962683/2147483648) 0 8 ![60,0,4] ![(25/128),0,(1/2)] ![(1/128),1,(1/4)] affine01261
theorem leaf01261_checked : FastNestedCellData.accepts 1 2 4 leaf01261=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1707842631/500000000000) (4554348583/4294967296) (62962683/2147483648) 0 8 ![60,0,4] ![(25/128),0,(1/2)] ![(1/128),1,(1/4)] 15752067966113889280849870848000000000000 16760418907861047986032108884812730728448 4906897920110839529111189192704000000000000 raw01261 affine01261
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01261_raw leaf01261_rectangular
    leaf01261_transform leaf01261_sign leaf01261_log
#print axioms leaf01261_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
