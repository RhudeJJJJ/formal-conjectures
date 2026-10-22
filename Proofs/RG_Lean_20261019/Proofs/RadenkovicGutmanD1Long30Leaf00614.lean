/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00614 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 86947410855248357226413293568000000000000 73546043681136247898335919362454090416128 975219555184928119808795344896000000000000))
theorem leaf00614_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 86947410855248357226413293568000000000000 73546043681136247898335919362454090416128 975219555184928119808795344896000000000000 raw00614=true := by decide +kernel
#print axioms leaf00614_raw
theorem leaf00614_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00614=true := by decide +kernel
#print axioms leaf00614_rectangular
def affine00614 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00614 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00614_transform : affine00614=(NestedInteger.clearedAll 3 raw00614 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00614_transform
theorem leaf00614_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00614=true := by decide +kernel
#print axioms leaf00614_sign
theorem leaf00614_log : RationalLog.accepts (844552203/1073741824) (-515607229/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00614_log
def leaf00614 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (75414857393/1000000000000) (844552203/1073741824) (-515607229/4294967296) 1 8 ![60,0,4] ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00614
theorem leaf00614_checked : FastNestedCellData.accepts 1 2 4 leaf00614=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (75414857393/1000000000000) (844552203/1073741824) (-515607229/4294967296) 1 8 ![60,0,4] ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)] 86947410855248357226413293568000000000000 73546043681136247898335919362454090416128 975219555184928119808795344896000000000000 raw00614 affine00614
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00614_raw leaf00614_rectangular
    leaf00614_transform leaf00614_sign leaf00614_log
#print axioms leaf00614_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
