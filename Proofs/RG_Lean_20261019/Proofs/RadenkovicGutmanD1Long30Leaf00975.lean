/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00975 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 31390482686203087103033606144000000000000 12019727388142570240667210170802588614656 16350558795788449723252211712000000000000))
theorem leaf00975_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 31390482686203087103033606144000000000000 12019727388142570240667210170802588614656 16350558795788449723252211712000000000000 raw00975=true := by decide +kernel
#print axioms leaf00975_raw
theorem leaf00975_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00975=true := by decide +kernel
#print axioms leaf00975_rectangular
def affine00975 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00975 (IntegerComputedClassCell.leftNumerator ![(19/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/160),0,0] ![(1/160),1,(1/16)]))
theorem leaf00975_transform : affine00975=(NestedInteger.clearedAll 3 raw00975 (IntegerComputedClassCell.leftNumerator ![(19/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/160),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00975_transform
theorem leaf00975_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00975=true := by decide +kernel
#print axioms leaf00975_sign
theorem leaf00975_log : RationalLog.accepts (236954727/1073741824) (-3244924695/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00975_log
def leaf00975 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (735126397713/1000000000000) (236954727/1073741824) (-3244924695/4294967296) 3 8 ![60,0,4] ![(19/160),0,0] ![(1/160),1,(1/16)] affine00975
theorem leaf00975_checked : FastNestedCellData.accepts 1 2 4 leaf00975=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (735126397713/1000000000000) (236954727/1073741824) (-3244924695/4294967296) 3 8 ![60,0,4] ![(19/160),0,0] ![(1/160),1,(1/16)] 31390482686203087103033606144000000000000 12019727388142570240667210170802588614656 16350558795788449723252211712000000000000 raw00975 affine00975
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00975_raw leaf00975_rectangular
    leaf00975_transform leaf00975_sign leaf00975_log
#print axioms leaf00975_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
