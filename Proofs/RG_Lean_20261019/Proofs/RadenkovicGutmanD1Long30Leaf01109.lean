/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01109 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 903389080442093594894078574592000000000000 1059692239841383757724912821209296736878592 5409593708970851107507120635904000000000000))
theorem leaf01109_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 903389080442093594894078574592000000000000 1059692239841383757724912821209296736878592 5409593708970851107507120635904000000000000 raw01109=true := by decide +kernel
#print axioms leaf01109_raw
theorem leaf01109_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01109=true := by decide +kernel
#print axioms leaf01109_rectangular
def affine01109 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01109 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01109_transform : affine01109=(NestedInteger.clearedAll 3 raw01109 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01109_transform
theorem leaf01109_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01109=true := by decide +kernel
#print axioms leaf01109_sign
theorem leaf01109_log : RationalLog.accepts (2106410851/2147483648) (-41470695/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01109_log
def leaf01109 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (195891280723/1000000000000) (2106410851/2147483648) (-41470695/4294967296) 1 8 ![60,0,4] ![(9/16),0,(15/16)] ![(1/32),1,(1/16)] affine01109
theorem leaf01109_checked : FastNestedCellData.accepts 1 2 4 leaf01109=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (195891280723/1000000000000) (2106410851/2147483648) (-41470695/4294967296) 1 8 ![60,0,4] ![(9/16),0,(15/16)] ![(1/32),1,(1/16)] 903389080442093594894078574592000000000000 1059692239841383757724912821209296736878592 5409593708970851107507120635904000000000000 raw01109 affine01109
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01109_raw leaf01109_rectangular
    leaf01109_transform leaf01109_sign leaf01109_log
#print axioms leaf01109_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
