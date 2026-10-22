/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01178 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 165244758363916040114544836608000000000000 203096147320705670504443396042798844084224 5668050667801957052564648230912000000000000))
theorem leaf01178_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 165244758363916040114544836608000000000000 203096147320705670504443396042798844084224 5668050667801957052564648230912000000000000 raw01178=true := by decide +kernel
#print axioms leaf01178_raw
theorem leaf01178_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01178=true := by decide +kernel
#print axioms leaf01178_rectangular
def affine01178 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01178 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01178_transform : affine01178=(NestedInteger.clearedAll 3 raw01178 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01178_transform
theorem leaf01178_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01178=true := by decide +kernel
#print axioms leaf01178_sign
theorem leaf01178_log : RationalLog.accepts (5096178569/4294967296) (367320673/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01178_log
def leaf01178 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (17915872601/500000000000) (5096178569/4294967296) (367320673/4294967296) 0 8 ![60,0,4] ![(1/2),0,(7/8)] ![(1/16),1,(1/16)] affine01178
theorem leaf01178_checked : FastNestedCellData.accepts 1 2 4 leaf01178=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (17915872601/500000000000) (5096178569/4294967296) (367320673/4294967296) 0 8 ![60,0,4] ![(1/2),0,(7/8)] ![(1/16),1,(1/16)] 165244758363916040114544836608000000000000 203096147320705670504443396042798844084224 5668050667801957052564648230912000000000000 raw01178 affine01178
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01178_raw leaf01178_rectangular
    leaf01178_transform leaf01178_sign leaf01178_log
#print axioms leaf01178_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
