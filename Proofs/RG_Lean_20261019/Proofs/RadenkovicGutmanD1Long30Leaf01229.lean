/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01229 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 10230824967654546549506048000000000000 11405864595245901215811458473062825984 1255212744411850351199649792000000000000))
theorem leaf01229_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 10230824967654546549506048000000000000 11405864595245901215811458473062825984 1255212744411850351199649792000000000000 raw01229=true := by decide +kernel
#print axioms leaf01229_raw
theorem leaf01229_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01229=true := by decide +kernel
#print axioms leaf01229_rectangular
def affine01229 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01229 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01229_transform : affine01229=(NestedInteger.clearedAll 3 raw01229 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/32),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01229_transform
theorem leaf01229_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01229=true := by decide +kernel
#print axioms leaf01229_sign
theorem leaf01229_log : RationalLog.accepts (4745138509/4294967296) (107027021/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01229_log
def leaf01229 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (70990609/7812500000) (4745138509/4294967296) (107027021/2147483648) 0 8 ![60,0,4] ![(9/32),0,(15/16)] ![(1/64),1,(1/16)] affine01229
theorem leaf01229_checked : FastNestedCellData.accepts 1 2 4 leaf01229=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (70990609/7812500000) (4745138509/4294967296) (107027021/2147483648) 0 8 ![60,0,4] ![(9/32),0,(15/16)] ![(1/64),1,(1/16)] 10230824967654546549506048000000000000 11405864595245901215811458473062825984 1255212744411850351199649792000000000000 raw01229 affine01229
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01229_raw leaf01229_rectangular
    leaf01229_transform leaf01229_sign leaf01229_log
#print axioms leaf01229_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
