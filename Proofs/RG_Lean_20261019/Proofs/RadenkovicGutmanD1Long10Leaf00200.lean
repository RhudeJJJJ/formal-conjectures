/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00200 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2079831962248856627763478528000000000000 1624389488986931937471141942261517910016 14069597986937309913937870848000000000000))
theorem leaf00200_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2079831962248856627763478528000000000000 1624389488986931937471141942261517910016 14069597986937309913937870848000000000000 raw00200=true := by decide +kernel
#print axioms leaf00200_raw
theorem leaf00200_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00200=true := by decide +kernel
#print axioms leaf00200_rectangular
def affine00200 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00200 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00200_transform : affine00200=(NestedInteger.clearedAll 3 raw00200 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00200_transform
theorem leaf00200_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00200=true := by decide +kernel
#print axioms leaf00200_sign
theorem leaf00200_log : RationalLog.accepts (3007254411/4294967296) (-191349625/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00200_log
def leaf00200 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (3607933331/31250000000) (3007254411/4294967296) (-191349625/1073741824) 1 8 ![52,0,4] ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00200
theorem leaf00200_checked : FastNestedCellData.accepts 1 0 4 leaf00200=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (3607933331/31250000000) (3007254411/4294967296) (-191349625/1073741824) 1 8 ![52,0,4] ![(103/3200),0,(1/2)] ![(3/3200),1,(1/2)] 2079831962248856627763478528000000000000 1624389488986931937471141942261517910016 14069597986937309913937870848000000000000 raw00200 affine00200
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00200_raw leaf00200_rectangular
    leaf00200_transform leaf00200_sign leaf00200_log
#print axioms leaf00200_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
