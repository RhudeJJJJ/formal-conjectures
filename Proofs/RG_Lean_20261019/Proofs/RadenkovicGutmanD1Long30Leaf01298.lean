/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01298 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000))
theorem leaf01298_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000 raw01298=true := by decide +kernel
#print axioms leaf01298_raw
theorem leaf01298_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01298=true := by decide +kernel
#print axioms leaf01298_rectangular
def affine01298 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01298 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01298_transform : affine01298=(NestedInteger.clearedAll 3 raw01298 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/64),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01298_transform
theorem leaf01298_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01298=true := by decide +kernel
#print axioms leaf01298_sign
theorem leaf01298_log : RationalLog.accepts (2221162147/2147483648) (36221379/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01298_log
def leaf01298 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1393684741/1000000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(7/8)] ![(1/128),1,(1/16)] affine01298
theorem leaf01298_checked : FastNestedCellData.accepts 1 2 4 leaf01298=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1393684741/1000000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(7/8)] ![(1/128),1,(1/16)] 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000 raw01298 affine01298
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01298_raw leaf01298_rectangular
    leaf01298_transform leaf01298_sign leaf01298_log
#print axioms leaf01298_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
