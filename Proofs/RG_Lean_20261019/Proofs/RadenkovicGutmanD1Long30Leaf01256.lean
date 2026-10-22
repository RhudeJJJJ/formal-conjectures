/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01256 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2798427150394374242442202316800000000000 2989875864422864720977077480390643417088 788349625258561159293810665062400000000000))
theorem leaf01256_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2798427150394374242442202316800000000000 2989875864422864720977077480390643417088 788349625258561159293810665062400000000000 raw01256=true := by decide +kernel
#print axioms leaf01256_raw
theorem leaf01256_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01256=true := by decide +kernel
#print axioms leaf01256_rectangular
def affine01256 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01256 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01256_transform : affine01256=(NestedInteger.clearedAll 3 raw01256 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01256_transform
theorem leaf01256_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01256=true := by decide +kernel
#print axioms leaf01256_sign
theorem leaf01256_log : RationalLog.accepts (4571461153/4294967296) (33494807/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01256_log
def leaf01256 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (758515199/200000000000) (4571461153/4294967296) (33494807/1073741824) 0 8 ![60,0,4] ![(13/64),0,(1/2)] ![(1/128),1,(1/4)] affine01256
theorem leaf01256_checked : FastNestedCellData.accepts 1 2 4 leaf01256=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (758515199/200000000000) (4571461153/4294967296) (33494807/1073741824) 0 8 ![60,0,4] ![(13/64),0,(1/2)] ![(1/128),1,(1/4)] 2798427150394374242442202316800000000000 2989875864422864720977077480390643417088 788349625258561159293810665062400000000000 raw01256 affine01256
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01256_raw leaf01256_rectangular
    leaf01256_transform leaf01256_sign leaf01256_log
#print axioms leaf01256_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
