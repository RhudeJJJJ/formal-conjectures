/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00985 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 814254783750263223119117287424000000000000 357327260181600713877162835714239306399744 505947635392667348685507526656000000000000))
theorem leaf00985_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 814254783750263223119117287424000000000000 357327260181600713877162835714239306399744 505947635392667348685507526656000000000000 raw00985=true := by decide +kernel
#print axioms leaf00985_raw
theorem leaf00985_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00985=true := by decide +kernel
#print axioms leaf00985_rectangular
def affine00985 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00985 (IntegerComputedClassCell.leftNumerator ![(21/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/160),0,0] ![(1/160),1,(1/16)]))
theorem leaf00985_transform : affine00985=(NestedInteger.clearedAll 3 raw00985 (IntegerComputedClassCell.leftNumerator ![(21/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/160),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00985_transform
theorem leaf00985_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00985=true := by decide +kernel
#print axioms leaf00985_sign
theorem leaf00985_log : RationalLog.accepts (276160881/1073741824) (-1458056887/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00985_log
def leaf00985 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (706253444399/1000000000000) (276160881/1073741824) (-1458056887/2147483648) 2 8 ![60,0,4] ![(21/160),0,0] ![(1/160),1,(1/16)] affine00985
theorem leaf00985_checked : FastNestedCellData.accepts 1 2 4 leaf00985=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (706253444399/1000000000000) (276160881/1073741824) (-1458056887/2147483648) 2 8 ![60,0,4] ![(21/160),0,0] ![(1/160),1,(1/16)] 814254783750263223119117287424000000000000 357327260181600713877162835714239306399744 505947635392667348685507526656000000000000 raw00985 affine00985
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00985_raw leaf00985_rectangular
    leaf00985_transform leaf00985_sign leaf00985_log
#print axioms leaf00985_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
