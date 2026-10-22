/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01348 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 16806845127626438815934054400000000000 16839345673046879420462610076554756096 924120790191672482184059420672000000000000))
theorem leaf01348_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 16806845127626438815934054400000000000 16839345673046879420462610076554756096 924120790191672482184059420672000000000000 raw01348=true := by decide +kernel
#print axioms leaf01348_raw
theorem leaf01348_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01348=true := by decide +kernel
#print axioms leaf01348_rectangular
def affine01348 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01348 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(1/256),1,1]))
theorem leaf01348_transform : affine01348=(NestedInteger.clearedAll 3 raw01348 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01348_transform
theorem leaf01348_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01348=true := by decide +kernel
#print axioms leaf01348_sign
theorem leaf01348_log : RationalLog.accepts (4303194355/4294967296) (2054797/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01348_log
def leaf01348 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (9111009/500000000000) (4303194355/4294967296) (2054797/2147483648) 0 8 ![60,0,4] ![(1/32),0,0] ![(1/256),1,1] affine01348
theorem leaf01348_checked : FastNestedCellData.accepts 1 2 4 leaf01348=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (9111009/500000000000) (4303194355/4294967296) (2054797/2147483648) 0 8 ![60,0,4] ![(1/32),0,0] ![(1/256),1,1] 16806845127626438815934054400000000000 16839345673046879420462610076554756096 924120790191672482184059420672000000000000 raw01348 affine01348
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01348_raw leaf01348_rectangular
    leaf01348_transform leaf01348_sign leaf01348_log
#print axioms leaf01348_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
