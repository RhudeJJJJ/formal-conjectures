/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01045 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 337901462606503007122678297395200000000000 288821555028038263957955653449632282836992 630694791016924906040217462374400000000000))
theorem leaf01045_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 337901462606503007122678297395200000000000 288821555028038263957955653449632282836992 630694791016924906040217462374400000000000 raw01045=true := by decide +kernel
#print axioms leaf01045_raw
theorem leaf01045_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01045=true := by decide +kernel
#print axioms leaf01045_rectangular
def affine01045 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01045 (IntegerComputedClassCell.leftNumerator ![(41/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/160),0,0] ![(3/160),1,(1/16)]))
theorem leaf01045_transform : affine01045=(NestedInteger.clearedAll 3 raw01045 (IntegerComputedClassCell.leftNumerator ![(41/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/160),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01045_transform
theorem leaf01045_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01045=true := by decide +kernel
#print axioms leaf01045_sign
theorem leaf01045_log : RationalLog.accepts (2518020037/4294967296) (-573347065/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01045_log
def leaf01045 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (91588374961/200000000000) (2518020037/4294967296) (-573347065/2147483648) 1 8 ![60,0,4] ![(41/160),0,0] ![(3/160),1,(1/16)] affine01045
theorem leaf01045_checked : FastNestedCellData.accepts 1 2 4 leaf01045=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (91588374961/200000000000) (2518020037/4294967296) (-573347065/2147483648) 1 8 ![60,0,4] ![(41/160),0,0] ![(3/160),1,(1/16)] 337901462606503007122678297395200000000000 288821555028038263957955653449632282836992 630694791016924906040217462374400000000000 raw01045 affine01045
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01045_raw leaf01045_rectangular
    leaf01045_transform leaf01045_sign leaf01045_log
#print axioms leaf01045_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
