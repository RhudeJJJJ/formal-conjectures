/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01292 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1865884350344305411115450368000000000000 1939500184802198989197385791307918606336 1198408395908776729808472113152000000000000))
theorem leaf01292_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1865884350344305411115450368000000000000 1939500184802198989197385791307918606336 1198408395908776729808472113152000000000000 raw01292=true := by decide +kernel
#print axioms leaf01292_raw
theorem leaf01292_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01292=true := by decide +kernel
#print axioms leaf01292_rectangular
def affine01292 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01292 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01292_transform : affine01292=(NestedInteger.clearedAll 3 raw01292 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01292_transform
theorem leaf01292_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01292=true := by decide +kernel
#print axioms leaf01292_sign
theorem leaf01292_log : RationalLog.accepts (1114301411/1073741824) (79624595/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01292_log
def leaf01292 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1618396693/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(3/4)] ![(1/128),1,(1/8)] affine01292
theorem leaf01292_checked : FastNestedCellData.accepts 1 2 4 leaf01292=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1618396693/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(3/4)] ![(1/128),1,(1/8)] 1865884350344305411115450368000000000000 1939500184802198989197385791307918606336 1198408395908776729808472113152000000000000 raw01292 affine01292
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01292_raw leaf01292_rectangular
    leaf01292_transform leaf01292_sign leaf01292_log
#print axioms leaf01292_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
