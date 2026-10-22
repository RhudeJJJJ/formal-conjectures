/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00404 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 684218321606359013114922401792000000000000 628333052583198583472392303839478636609536 16940059405078679322482366742528000000000000))
theorem leaf00404_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 684218321606359013114922401792000000000000 628333052583198583472392303839478636609536 16940059405078679322482366742528000000000000 raw00404=true := by decide +kernel
#print axioms leaf00404_raw
theorem leaf00404_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00404=true := by decide +kernel
#print axioms leaf00404_rectangular
def affine00404 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00404 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00404_transform : affine00404=(NestedInteger.clearedAll 3 raw00404 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00404_transform
theorem leaf00404_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00404=true := by decide +kernel
#print axioms leaf00404_sign
theorem leaf00404_log : RationalLog.accepts (3803101989/4294967296) (-261191803/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00404_log
def leaf00404 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (37091549537/1000000000000) (3803101989/4294967296) (-261191803/4294967296) 1 8 ![60,0,4] ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)] affine00404
theorem leaf00404_checked : FastNestedCellData.accepts 1 2 4 leaf00404=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (37091549537/1000000000000) (3803101989/4294967296) (-261191803/4294967296) 1 8 ![60,0,4] ![(1/100),0,(1/2)] ![(1/6400),1,(1/2)] 684218321606359013114922401792000000000000 628333052583198583472392303839478636609536 16940059405078679322482366742528000000000000 raw00404 affine00404
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00404_raw leaf00404_rectangular
    leaf00404_transform leaf00404_sign leaf00404_log
#print axioms leaf00404_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
