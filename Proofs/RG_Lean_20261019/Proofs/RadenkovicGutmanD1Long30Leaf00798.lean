/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00798 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1687404458138050708138622976000000000000 981798206201599552289304890922051305472 3493828259354443434181001216000000000000))
theorem leaf00798_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1687404458138050708138622976000000000000 981798206201599552289304890922051305472 3493828259354443434181001216000000000000 raw00798=true := by decide +kernel
#print axioms leaf00798_raw
theorem leaf00798_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00798=true := by decide +kernel
#print axioms leaf00798_rectangular
def affine00798 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00798 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00798_transform : affine00798=(NestedInteger.clearedAll 3 raw00798 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00798_transform
theorem leaf00798_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00798=true := by decide +kernel
#print axioms leaf00798_sign
theorem leaf00798_log : RationalLog.accepts (1950790461/4294967296) (-423703527/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00798_log
def leaf00798 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8781540381/31250000000) (1950790461/4294967296) (-423703527/1073741824) 2 8 ![60,0,4] ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00798
theorem leaf00798_checked : FastNestedCellData.accepts 1 2 4 leaf00798=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8781540381/31250000000) (1950790461/4294967296) (-423703527/1073741824) 2 8 ![60,0,4] ![(133/3200),0,(1/4)] ![(3/3200),1,(1/4)] 1687404458138050708138622976000000000000 981798206201599552289304890922051305472 3493828259354443434181001216000000000000 raw00798 affine00798
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00798_raw leaf00798_rectangular
    leaf00798_transform leaf00798_sign leaf00798_log
#print axioms leaf00798_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
