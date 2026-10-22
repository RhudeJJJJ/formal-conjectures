/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00797 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4438059394327889693312087490560000000000 1777875272433548734842426904870756810752 3694859310296029254903241113600000000000))
theorem leaf00797_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4438059394327889693312087490560000000000 1777875272433548734842426904870756810752 3694859310296029254903241113600000000000 raw00797=true := by decide +kernel
#print axioms leaf00797_raw
theorem leaf00797_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00797=true := by decide +kernel
#print axioms leaf00797_rectangular
def affine00797 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00797 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00797_transform : affine00797=(NestedInteger.clearedAll 3 raw00797 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00797_transform
theorem leaf00797_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00797=true := by decide +kernel
#print axioms leaf00797_sign
theorem leaf00797_log : RationalLog.accepts (290403315/1073741824) (-2808123049/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00797_log
def leaf00797 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (96235072739/200000000000) (290403315/1073741824) (-2808123049/4294967296) 2 8 ![60,0,4] ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00797
theorem leaf00797_checked : FastNestedCellData.accepts 1 2 4 leaf00797=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (96235072739/200000000000) (290403315/1073741824) (-2808123049/4294967296) 2 8 ![60,0,4] ![(133/3200),0,(1/8)] ![(3/3200),1,(1/8)] 4438059394327889693312087490560000000000 1777875272433548734842426904870756810752 3694859310296029254903241113600000000000 raw00797 affine00797
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00797_raw leaf00797_rectangular
    leaf00797_transform leaf00797_sign leaf00797_log
#print axioms leaf00797_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
