/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01185 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 119292045411142363041744551936000000000000 143240032074328391624369152964967851360256 5537486182918363776189814800384000000000000))
theorem leaf01185_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 119292045411142363041744551936000000000000 143240032074328391624369152964967851360256 5537486182918363776189814800384000000000000 raw01185=true := by decide +kernel
#print axioms leaf01185_raw
theorem leaf01185_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01185=true := by decide +kernel
#print axioms leaf01185_rectangular
def affine01185 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01185 (IntegerComputedClassCell.leftNumerator ![(7/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/16),0,0] ![(1/32),1,(1/2)]))
theorem leaf01185_transform : affine01185=(NestedInteger.clearedAll 3 raw01185 (IntegerComputedClassCell.leftNumerator ![(7/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/16),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01185_transform
theorem leaf01185_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01185=true := by decide +kernel
#print axioms leaf01185_sign
theorem leaf01185_log : RationalLog.accepts (2513573487/2147483648) (169016283/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01185_log
def leaf01185 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (25867338959/1000000000000) (2513573487/2147483648) (169016283/2147483648) 0 8 ![60,0,4] ![(7/16),0,0] ![(1/32),1,(1/2)] affine01185
theorem leaf01185_checked : FastNestedCellData.accepts 1 2 4 leaf01185=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (25867338959/1000000000000) (2513573487/2147483648) (169016283/2147483648) 0 8 ![60,0,4] ![(7/16),0,0] ![(1/32),1,(1/2)] 119292045411142363041744551936000000000000 143240032074328391624369152964967851360256 5537486182918363776189814800384000000000000 raw01185 affine01185
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01185_raw leaf01185_rectangular
    leaf01185_transform leaf01185_sign leaf01185_log
#print axioms leaf01185_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
