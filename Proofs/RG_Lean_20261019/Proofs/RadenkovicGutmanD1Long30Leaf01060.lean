/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01060 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4461862781237580693369362841600000000000 4312251375020283134649072452197391794176 11142627165581142196028545433600000000000))
theorem leaf01060_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4461862781237580693369362841600000000000 4312251375020283134649072452197391794176 11142627165581142196028545433600000000000 raw01060=true := by decide +kernel
#print axioms leaf01060_raw
theorem leaf01060_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01060=true := by decide +kernel
#print axioms leaf01060_rectangular
def affine01060 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01060 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(3/160),1,(1/16)]))
theorem leaf01060_transform : affine01060=(NestedInteger.clearedAll 3 raw01060 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01060_transform
theorem leaf01060_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01060=true := by decide +kernel
#print axioms leaf01060_sign
theorem leaf01060_log : RationalLog.accepts (1496372533/2147483648) (-775784715/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01060_log
def leaf01060 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19350245283/50000000000) (1496372533/2147483648) (-775784715/4294967296) 1 8 ![60,0,4] ![(5/16),0,0] ![(3/160),1,(1/16)] affine01060
theorem leaf01060_checked : FastNestedCellData.accepts 1 2 4 leaf01060=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19350245283/50000000000) (1496372533/2147483648) (-775784715/4294967296) 1 8 ![60,0,4] ![(5/16),0,0] ![(3/160),1,(1/16)] 4461862781237580693369362841600000000000 4312251375020283134649072452197391794176 11142627165581142196028545433600000000000 raw01060 affine01060
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01060_raw leaf01060_rectangular
    leaf01060_transform leaf01060_sign leaf01060_log
#print axioms leaf01060_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
