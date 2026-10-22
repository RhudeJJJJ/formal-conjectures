/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00641 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10171991805714121808306354782208000000000000 3136818543407173393458472455657037781532672 5688570142515580967987806470144000000000000))
theorem leaf00641_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10171991805714121808306354782208000000000000 3136818543407173393458472455657037781532672 5688570142515580967987806470144000000000000 raw00641=true := by decide +kernel
#print axioms leaf00641_raw
theorem leaf00641_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00641=true := by decide +kernel
#print axioms leaf00641_rectangular
def affine00641 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00641 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00641_transform : affine00641=(NestedInteger.clearedAll 3 raw00641 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00641_transform
theorem leaf00641_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00641=true := by decide +kernel
#print axioms leaf00641_sign
theorem leaf00641_log : RationalLog.accepts (853714253/4294967296) (-867370111/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00641_log
def leaf00641 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (551424780713/1000000000000) (853714253/4294967296) (-867370111/1073741824) 3 8 ![60,0,4] ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00641
theorem leaf00641_checked : FastNestedCellData.accepts 1 2 4 leaf00641=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (551424780713/1000000000000) (853714253/4294967296) (-867370111/1073741824) 3 8 ![60,0,4] ![(149/6400),0,(1/16)] ![(3/6400),1,(1/16)] 10171991805714121808306354782208000000000000 3136818543407173393458472455657037781532672 5688570142515580967987806470144000000000000 raw00641 affine00641
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00641_raw leaf00641_rectangular
    leaf00641_transform leaf00641_sign leaf00641_log
#print axioms leaf00641_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
