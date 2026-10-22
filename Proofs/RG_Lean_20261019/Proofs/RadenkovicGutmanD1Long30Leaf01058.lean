/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01058 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 103330470806631623548622340096000000000000 96132346721084956945120425626930251825152 268151903687898495135858556928000000000000))
theorem leaf01058_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 103330470806631623548622340096000000000000 96132346721084956945120425626930251825152 268151903687898495135858556928000000000000 raw01058=true := by decide +kernel
#print axioms leaf01058_raw
theorem leaf01058_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01058=true := by decide +kernel
#print axioms leaf01058_rectangular
def affine01058 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01058 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01058_transform : affine01058=(NestedInteger.clearedAll 3 raw01058 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01058_transform
theorem leaf01058_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01058=true := by decide +kernel
#print axioms leaf01058_sign
theorem leaf01058_log : RationalLog.accepts (2941314653/4294967296) (-813010069/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01058_log
def leaf01058 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (44812448373/125000000000) (2941314653/4294967296) (-813010069/4294967296) 1 8 ![60,0,4] ![(47/160),0,(1/4)] ![(3/160),1,(1/4)] affine01058
theorem leaf01058_checked : FastNestedCellData.accepts 1 2 4 leaf01058=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (44812448373/125000000000) (2941314653/4294967296) (-813010069/4294967296) 1 8 ![60,0,4] ![(47/160),0,(1/4)] ![(3/160),1,(1/4)] 103330470806631623548622340096000000000000 96132346721084956945120425626930251825152 268151903687898495135858556928000000000000 raw01058 affine01058
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01058_raw leaf01058_rectangular
    leaf01058_transform leaf01058_sign leaf01058_log
#print axioms leaf01058_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
