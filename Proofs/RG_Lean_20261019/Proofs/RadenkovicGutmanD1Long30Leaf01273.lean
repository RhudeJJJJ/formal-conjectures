/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01273 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 65547283154724673795653632000000000000 69181331183222593402218001057053671424 25350861431520037488174301184000000000000))
theorem leaf01273_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 65547283154724673795653632000000000000 69181331183222593402218001057053671424 25350861431520037488174301184000000000000 raw01273=true := by decide +kernel
#print axioms leaf01273_raw
theorem leaf01273_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01273=true := by decide +kernel
#print axioms leaf01273_rectangular
def affine01273 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01273 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01273_transform : affine01273=(NestedInteger.clearedAll 3 raw01273 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01273_transform
theorem leaf01273_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01273=true := by decide +kernel
#print axioms leaf01273_sign
theorem leaf01273_log : RationalLog.accepts (282546897/268435456) (27506069/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01273_log
def leaf01273 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2728953861/1000000000000) (282546897/268435456) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(7/8)] ![(1/128),1,(1/16)] affine01273
theorem leaf01273_checked : FastNestedCellData.accepts 1 2 4 leaf01273=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2728953861/1000000000000) (282546897/268435456) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(7/8)] ![(1/128),1,(1/16)] 65547283154724673795653632000000000000 69181331183222593402218001057053671424 25350861431520037488174301184000000000000 raw01273 affine01273
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01273_raw leaf01273_rectangular
    leaf01273_transform leaf01273_sign leaf01273_log
#print axioms leaf01273_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
