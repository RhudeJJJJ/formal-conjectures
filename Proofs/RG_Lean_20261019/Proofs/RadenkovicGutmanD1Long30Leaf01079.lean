/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01079 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 431643796296909671737902235648000000000000 442198490966335534611704077271851421663232 1574817488906526952481580122112000000000000))
theorem leaf01079_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 431643796296909671737902235648000000000000 442198490966335534611704077271851421663232 1574817488906526952481580122112000000000000 raw01079=true := by decide +kernel
#print axioms leaf01079_raw
theorem leaf01079_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01079=true := by decide +kernel
#print axioms leaf01079_rectangular
def affine01079 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01079 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01079_transform : affine01079=(NestedInteger.clearedAll 3 raw01079 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01079_transform
theorem leaf01079_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01079=true := by decide +kernel
#print axioms leaf01079_sign
theorem leaf01079_log : RationalLog.accepts (1717680987/2147483648) (-119894903/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01079_log
def leaf01079 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (280793485011/1000000000000) (1717680987/2147483648) (-119894903/1073741824) 1 8 ![60,0,4] ![(59/160),0,(1/2)] ![(3/160),1,(1/2)] affine01079
theorem leaf01079_checked : FastNestedCellData.accepts 1 2 4 leaf01079=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (280793485011/1000000000000) (1717680987/2147483648) (-119894903/1073741824) 1 8 ![60,0,4] ![(59/160),0,(1/2)] ![(3/160),1,(1/2)] 431643796296909671737902235648000000000000 442198490966335534611704077271851421663232 1574817488906526952481580122112000000000000 raw01079 affine01079
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01079_raw leaf01079_rectangular
    leaf01079_transform leaf01079_sign leaf01079_log
#print axioms leaf01079_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
