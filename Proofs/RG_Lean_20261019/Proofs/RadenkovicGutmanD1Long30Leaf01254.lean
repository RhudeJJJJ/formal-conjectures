/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01254 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 78661197852103306484121600000000000 84393681534559182619550118831980544 20132509371926540594446336000000000000))
theorem leaf01254_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 78661197852103306484121600000000000 84393681534559182619550118831980544 20132509371926540594446336000000000000 raw01254=true := by decide +kernel
#print axioms leaf01254_raw
theorem leaf01254_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01254=true := by decide +kernel
#print axioms leaf01254_rectangular
def affine01254 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01254 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01254_transform : affine01254=(NestedInteger.clearedAll 3 raw01254 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01254_transform
theorem leaf01254_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01254=true := by decide +kernel
#print axioms leaf01254_sign
theorem leaf01254_log : RationalLog.accepts (286795635/268435456) (71038105/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01254_log
def leaf01254 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (261994419/62500000000) (286795635/268435456) (71038105/2147483648) 0 8 ![60,0,4] ![(27/128),0,(15/16)] ![(1/128),1,(1/16)] affine01254
theorem leaf01254_checked : FastNestedCellData.accepts 1 2 4 leaf01254=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (261994419/62500000000) (286795635/268435456) (71038105/2147483648) 0 8 ![60,0,4] ![(27/128),0,(15/16)] ![(1/128),1,(1/16)] 78661197852103306484121600000000000 84393681534559182619550118831980544 20132509371926540594446336000000000000 raw01254 affine01254
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01254_raw leaf01254_rectangular
    leaf01254_transform leaf01254_sign leaf01254_log
#print axioms leaf01254_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
