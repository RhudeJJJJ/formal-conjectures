/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01338 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 852428060424640430430224384000000000000 860577921718995876978415887767184605184 4655777248090309404452091592704000000000000))
theorem leaf01338_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 852428060424640430430224384000000000000 860577921718995876978415887767184605184 4655777248090309404452091592704000000000000 raw01338=true := by decide +kernel
#print axioms leaf01338_raw
theorem leaf01338_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01338=true := by decide +kernel
#print axioms leaf01338_rectangular
def affine01338 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01338 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/256),1,1]))
theorem leaf01338_transform : affine01338=(NestedInteger.clearedAll 3 raw01338 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01338_transform
theorem leaf01338_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01338=true := by decide +kernel
#print axioms leaf01338_sign
theorem leaf01338_log : RationalLog.accepts (2167614563/2147483648) (20037145/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01338_log
def leaf01338 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (184840871/1000000000000) (2167614563/2147483648) (20037145/4294967296) 0 8 ![60,0,4] ![(9/128),0,0] ![(1/256),1,1] affine01338
theorem leaf01338_checked : FastNestedCellData.accepts 1 2 4 leaf01338=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (184840871/1000000000000) (2167614563/2147483648) (20037145/4294967296) 0 8 ![60,0,4] ![(9/128),0,0] ![(1/256),1,1] 852428060424640430430224384000000000000 860577921718995876978415887767184605184 4655777248090309404452091592704000000000000 raw01338 affine01338
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01338_raw leaf01338_rectangular
    leaf01338_transform leaf01338_sign leaf01338_log
#print axioms leaf01338_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
