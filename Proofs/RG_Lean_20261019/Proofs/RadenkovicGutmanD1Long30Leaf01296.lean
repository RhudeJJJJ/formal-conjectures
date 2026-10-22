/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01296 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000))
theorem leaf01296_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000 raw01296=true := by decide +kernel
#print axioms leaf01296_raw
theorem leaf01296_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01296=true := by decide +kernel
#print axioms leaf01296_rectangular
def affine01296 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01296 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01296_transform : affine01296=(NestedInteger.clearedAll 3 raw01296 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01296_transform
theorem leaf01296_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01296=true := by decide +kernel
#print axioms leaf01296_sign
theorem leaf01296_log : RationalLog.accepts (2221162147/2147483648) (36221379/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01296_log
def leaf01296 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (696842371/500000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(1/2)] ![(1/128),1,(1/4)] affine01296
theorem leaf01296_checked : FastNestedCellData.accepts 1 2 4 leaf01296=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (696842371/500000000000) (2221162147/2147483648) (36221379/2147483648) 0 8 ![60,0,4] ![(9/64),0,(1/2)] ![(1/128),1,(1/4)] 1606809109694245339180040192000000000000 1664253701388949906816406532232467972096 1194139285044242743683855679488000000000000 raw01296 affine01296
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01296_raw leaf01296_rectangular
    leaf01296_transform leaf01296_sign leaf01296_log
#print axioms leaf01296_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
