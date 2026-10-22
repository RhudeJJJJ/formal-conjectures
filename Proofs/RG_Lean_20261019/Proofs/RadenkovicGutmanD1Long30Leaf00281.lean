/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00281 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3579636844706552054166629384192000000000000 2319414733678572869210289802994296974999552 11952511343777743447615283920896000000000000))
theorem leaf00281_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3579636844706552054166629384192000000000000 2319414733678572869210289802994296974999552 11952511343777743447615283920896000000000000 raw00281=true := by decide +kernel
#print axioms leaf00281_raw
theorem leaf00281_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00281=true := by decide +kernel
#print axioms leaf00281_rectangular
def affine00281 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00281 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00281_transform : affine00281=(NestedInteger.clearedAll 3 raw00281 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00281_transform
theorem leaf00281_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00281=true := by decide +kernel
#print axioms leaf00281_sign
theorem leaf00281_log : RationalLog.accepts (2330643673/4294967296) (-164094453/536870912) 1 8=true := by decide +kernel
#print axioms leaf00281_log
def leaf00281 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (194052502187/1000000000000) (2330643673/4294967296) (-164094453/536870912) 1 8 ![60,0,4] ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)] affine00281
theorem leaf00281_checked : FastNestedCellData.accepts 1 2 4 leaf00281=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (194052502187/1000000000000) (2330643673/4294967296) (-164094453/536870912) 1 8 ![60,0,4] ![(1/160),0,(1/16)] ![(1/6400),1,(1/16)] 3579636844706552054166629384192000000000000 2319414733678572869210289802994296974999552 11952511343777743447615283920896000000000000 raw00281 affine00281
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00281_raw leaf00281_rectangular
    leaf00281_transform leaf00281_sign leaf00281_log
#print axioms leaf00281_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
