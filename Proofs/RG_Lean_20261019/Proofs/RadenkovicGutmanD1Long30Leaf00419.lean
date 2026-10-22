/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00419 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 715822874031712252180993933312000000000000 654909929913631182970722181107126405955584 16877018473026059739462748864512000000000000))
theorem leaf00419_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 715822874031712252180993933312000000000000 654909929913631182970722181107126405955584 16877018473026059739462748864512000000000000 raw00419=true := by decide +kernel
#print axioms leaf00419_raw
theorem leaf00419_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00419=true := by decide +kernel
#print axioms leaf00419_rectangular
def affine00419 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00419 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00419_transform : affine00419=(NestedInteger.clearedAll 3 raw00419 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00419_transform
theorem leaf00419_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00419=true := by decide +kernel
#print axioms leaf00419_sign
theorem leaf00419_log : RationalLog.accepts (3782700021/4294967296) (-272743119/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00419_log
def leaf00419 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (38804835757/1000000000000) (3782700021/4294967296) (-272743119/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00419
theorem leaf00419_checked : FastNestedCellData.accepts 1 2 4 leaf00419=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (38804835757/1000000000000) (3782700021/4294967296) (-272743119/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/2)] ![(1/6400),1,(1/2)] 715822874031712252180993933312000000000000 654909929913631182970722181107126405955584 16877018473026059739462748864512000000000000 raw00419 affine00419
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00419_raw leaf00419_rectangular
    leaf00419_transform leaf00419_sign leaf00419_log
#print axioms leaf00419_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
