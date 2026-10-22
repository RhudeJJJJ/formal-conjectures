/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01297 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000))
theorem leaf01297_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000 raw01297=true := by decide +kernel
#print axioms leaf01297_raw
theorem leaf01297_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01297=true := by decide +kernel
#print axioms leaf01297_rectangular
def affine01297 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01297 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01297_transform : affine01297=(NestedInteger.clearedAll 3 raw01297 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/64),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01297_transform
theorem leaf01297_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01297=true := by decide +kernel
#print axioms leaf01297_sign
theorem leaf01297_log : RationalLog.accepts (2221162147/2147483648) (36221379/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01297_log
def leaf01297 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (696842371/500000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(3/4)] ![(1/128),1,(1/8)] affine01297
theorem leaf01297_checked : FastNestedCellData.accepts 1 2 4 leaf01297=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (696842371/500000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(3/4)] ![(1/128),1,(1/8)] 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000 raw01297 affine01297
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01297_raw leaf01297_rectangular
    leaf01297_transform leaf01297_sign leaf01297_log
#print axioms leaf01297_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
