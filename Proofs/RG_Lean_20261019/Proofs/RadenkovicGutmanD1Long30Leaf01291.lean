/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01291 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 466471087874306728930574336000000000000 484875046500635937870805514738598936576 299602098977493300459501256704000000000000))
theorem leaf01291_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 466471087874306728930574336000000000000 484875046500635937870805514738598936576 299602098977493300459501256704000000000000 raw01291=true := by decide +kernel
#print axioms leaf01291_raw
theorem leaf01291_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01291=true := by decide +kernel
#print axioms leaf01291_rectangular
def affine01291 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01291 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01291_transform : affine01291=(NestedInteger.clearedAll 3 raw01291 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01291_transform
theorem leaf01291_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01291=true := by decide +kernel
#print axioms leaf01291_sign
theorem leaf01291_log : RationalLog.accepts (1114301411/1073741824) (79624595/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01291_log
def leaf01291 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (809198347/500000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(1/2)] ![(1/128),1,(1/4)] affine01291
theorem leaf01291_checked : FastNestedCellData.accepts 1 2 4 leaf01291=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (809198347/500000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(1/2)] ![(1/128),1,(1/4)] 466471087874306728930574336000000000000 484875046500635937870805514738598936576 299602098977493300459501256704000000000000 raw01291 affine01291
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01291_raw leaf01291_rectangular
    leaf01291_transform leaf01291_sign leaf01291_log
#print axioms leaf01291_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
