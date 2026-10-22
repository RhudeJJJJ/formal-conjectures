/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01147 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 456080336853974660912026484736000000000000 583334501015537545167179015705583301951488 5898424784011223195293300293632000000000000))
theorem leaf01147_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 456080336853974660912026484736000000000000 583334501015537545167179015705583301951488 5898424784011223195293300293632000000000000 raw01147=true := by decide +kernel
#print axioms leaf01147_raw
theorem leaf01147_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01147=true := by decide +kernel
#print axioms leaf01147_rectangular
def affine01147 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01147 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01147_transform : affine01147=(NestedInteger.clearedAll 3 raw01147 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01147_transform
theorem leaf01147_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01147=true := by decide +kernel
#print axioms leaf01147_sign
theorem leaf01147_log : RationalLog.accepts (2499478051/2147483648) (162978085/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01147_log
def leaf01147 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (98896658409/1000000000000) (2499478051/2147483648) (162978085/2147483648) 0 8 ![60,0,4] ![(15/16),0,(3/4)] ![(1/16),1,(1/8)] affine01147
theorem leaf01147_checked : FastNestedCellData.accepts 1 2 4 leaf01147=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (98896658409/1000000000000) (2499478051/2147483648) (162978085/2147483648) 0 8 ![60,0,4] ![(15/16),0,(3/4)] ![(1/16),1,(1/8)] 456080336853974660912026484736000000000000 583334501015537545167179015705583301951488 5898424784011223195293300293632000000000000 raw01147 affine01147
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01147_raw leaf01147_rectangular
    leaf01147_transform leaf01147_sign leaf01147_log
#print axioms leaf01147_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
