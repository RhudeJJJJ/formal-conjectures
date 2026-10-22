/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00787 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 541383159052005732177493884928000000000000 219780742104388056818070649785347859283968 468041791906311637074136006656000000000000))
theorem leaf00787_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 541383159052005732177493884928000000000000 219780742104388056818070649785347859283968 468041791906311637074136006656000000000000 raw00787=true := by decide +kernel
#print axioms leaf00787_raw
theorem leaf00787_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00787=true := by decide +kernel
#print axioms leaf00787_rectangular
def affine00787 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00787 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00787_transform : affine00787=(NestedInteger.clearedAll 3 raw00787 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00787_transform
theorem leaf00787_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00787=true := by decide +kernel
#print axioms leaf00787_sign
theorem leaf00787_log : RationalLog.accepts (296614923/1073741824) (-2762673611/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00787_log
def leaf00787 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (469575037753/1000000000000) (296614923/1073741824) (-2762673611/4294967296) 2 8 ![60,0,4] ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00787
theorem leaf00787_checked : FastNestedCellData.accepts 1 2 4 leaf00787=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (469575037753/1000000000000) (296614923/1073741824) (-2762673611/4294967296) 2 8 ![60,0,4] ![(127/3200),0,(1/8)] ![(3/3200),1,(1/8)] 541383159052005732177493884928000000000000 219780742104388056818070649785347859283968 468041791906311637074136006656000000000000 raw00787 affine00787
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00787_raw leaf00787_rectangular
    leaf00787_transform leaf00787_sign leaf00787_log
#print axioms leaf00787_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
