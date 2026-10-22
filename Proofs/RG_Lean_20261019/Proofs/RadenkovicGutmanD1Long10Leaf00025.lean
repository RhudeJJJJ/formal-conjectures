/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00025 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 198670248885596876724093583360000000000 188461654467029772410794530590775312384 8749432607957076487328445235200000000000))
theorem leaf00025_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 198670248885596876724093583360000000000 188461654467029772410794530590775312384 8749432607957076487328445235200000000000 raw00025=true := by decide +kernel
#print axioms leaf00025_raw
theorem leaf00025_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00025=true := by decide +kernel
#print axioms leaf00025_rectangular
def affine00025 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00025 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00025_transform : affine00025=(NestedInteger.clearedAll 3 raw00025 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00025_transform
theorem leaf00025_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00025=true := by decide +kernel
#print axioms leaf00025_sign
theorem leaf00025_log : RationalLog.accepts (997090805/1073741824) (-159049149/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00025_log
def leaf00025 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4307974309/200000000000) (997090805/1073741824) (-159049149/4294967296) 1 8 ![52,0,4] ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)] affine00025
theorem leaf00025_checked : FastNestedCellData.accepts 1 0 4 leaf00025=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4307974309/200000000000) (997090805/1073741824) (-159049149/4294967296) 1 8 ![52,0,4] ![(11/4000),0,(1/4)] ![(3/16000),1,(1/4)] 198670248885596876724093583360000000000 188461654467029772410794530590775312384 8749432607957076487328445235200000000000 raw00025 affine00025
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00025_raw leaf00025_rectangular
    leaf00025_transform leaf00025_sign leaf00025_log
#print axioms leaf00025_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
