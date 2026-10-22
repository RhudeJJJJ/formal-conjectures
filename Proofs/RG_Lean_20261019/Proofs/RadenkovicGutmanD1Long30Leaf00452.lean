/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00452 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40535216756667752304765357260800000000000 27597404290532323806071297653588698857472 156987643948642299728067821568000000000000))
theorem leaf00452_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40535216756667752304765357260800000000000 27597404290532323806071297653588698857472 156987643948642299728067821568000000000000 raw00452=true := by decide +kernel
#print axioms leaf00452_raw
theorem leaf00452_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00452=true := by decide +kernel
#print axioms leaf00452_rectangular
def affine00452 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00452 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00452_transform : affine00452=(NestedInteger.clearedAll 3 raw00452 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00452_transform
theorem leaf00452_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00452=true := by decide +kernel
#print axioms leaf00452_sign
theorem leaf00452_log : RationalLog.accepts (621733915/1073741824) (-1173369311/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00452_log
def leaf00452 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (175793480279/1000000000000) (621733915/1073741824) (-1173369311/4294967296) 1 8 ![60,0,4] ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00452
theorem leaf00452_checked : FastNestedCellData.accepts 1 2 4 leaf00452=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (175793480279/1000000000000) (621733915/1073741824) (-1173369311/4294967296) 1 8 ![60,0,4] ![(37/3200),0,(1/8)] ![(1/6400),1,(1/8)] 40535216756667752304765357260800000000000 27597404290532323806071297653588698857472 156987643948642299728067821568000000000000 raw00452 affine00452
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00452_raw leaf00452_rectangular
    leaf00452_transform leaf00452_sign leaf00452_log
#print axioms leaf00452_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
