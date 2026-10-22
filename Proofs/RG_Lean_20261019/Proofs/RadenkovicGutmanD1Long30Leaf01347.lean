/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01347 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 29297849890099430617513984000000000000 29369419787820541348936594313317449728 1155737904939113853369913966592000000000000))
theorem leaf01347_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 29297849890099430617513984000000000000 29369419787820541348936594313317449728 1155737904939113853369913966592000000000000 raw01347=true := by decide +kernel
#print axioms leaf01347_raw
theorem leaf01347_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01347=true := by decide +kernel
#print axioms leaf01347_rectangular
def affine01347 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01347 (IntegerComputedClassCell.leftNumerator ![(9/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(9/256),0,0] ![(1/256),1,1]))
theorem leaf01347_transform : affine01347=(NestedInteger.clearedAll 3 raw01347 (IntegerComputedClassCell.leftNumerator ![(9/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(9/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(9/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01347_transform
theorem leaf01347_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01347=true := by decide +kernel
#print axioms leaf01347_sign
theorem leaf01347_log : RationalLog.accepts (2152674899/2147483648) (2592493/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01347_log
def leaf01347 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (12705917/500000000000) (2152674899/2147483648) (2592493/2147483648) 0 8 ![60,0,4] ![(9/256),0,0] ![(1/256),1,1] affine01347
theorem leaf01347_checked : FastNestedCellData.accepts 1 2 4 leaf01347=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (12705917/500000000000) (2152674899/2147483648) (2592493/2147483648) 0 8 ![60,0,4] ![(9/256),0,0] ![(1/256),1,1] 29297849890099430617513984000000000000 29369419787820541348936594313317449728 1155737904939113853369913966592000000000000 raw01347 affine01347
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01347_raw leaf01347_rectangular
    leaf01347_transform leaf01347_sign leaf01347_log
#print axioms leaf01347_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
