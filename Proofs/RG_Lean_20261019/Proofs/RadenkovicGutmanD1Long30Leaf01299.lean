/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01299 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000))
theorem leaf01299_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000 raw01299=true := by decide +kernel
#print axioms leaf01299_raw
theorem leaf01299_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01299=true := by decide +kernel
#print axioms leaf01299_rectangular
def affine01299 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01299 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01299_transform : affine01299=(NestedInteger.clearedAll 3 raw01299 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/64),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01299_transform
theorem leaf01299_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01299=true := by decide +kernel
#print axioms leaf01299_sign
theorem leaf01299_log : RationalLog.accepts (2221162147/2147483648) (36221379/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01299_log
def leaf01299 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1393684741/1000000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(15/16)] ![(1/128),1,(1/16)] affine01299
theorem leaf01299_checked : FastNestedCellData.accepts 1 2 4 leaf01299=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1393684741/1000000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(15/16)] ![(1/128),1,(1/16)] 6427236434165295338292772864000000000000 6657014800772594737155526344849265524736 4776557140172201065345183645696000000000000 raw01299 affine01299
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01299_raw leaf01299_rectangular
    leaf01299_transform leaf01299_sign leaf01299_log
#print axioms leaf01299_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
