/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00181 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1880580835146094566232922521600000000000 1425655319776999480410130371512692113408 11653624210914701908229121638400000000000))
theorem leaf00181_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1880580835146094566232922521600000000000 1425655319776999480410130371512692113408 11653624210914701908229121638400000000000 raw00181=true := by decide +kernel
#print axioms leaf00181_raw
theorem leaf00181_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00181=true := by decide +kernel
#print axioms leaf00181_rectangular
def affine00181 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00181 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00181_transform : affine00181=(NestedInteger.clearedAll 3 raw00181 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00181_transform
theorem leaf00181_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00181=true := by decide +kernel
#print axioms leaf00181_sign
theorem leaf00181_log : RationalLog.accepts (2901079179/4294967296) (-842589173/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00181_log
def leaf00181 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6116789481/50000000000) (2901079179/4294967296) (-842589173/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)] affine00181
theorem leaf00181_checked : FastNestedCellData.accepts 1 2 4 leaf00181=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6116789481/50000000000) (2901079179/4294967296) (-842589173/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/16)] ![(3/32000),1,(1/16)] 1880580835146094566232922521600000000000 1425655319776999480410130371512692113408 11653624210914701908229121638400000000000 raw00181 affine00181
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00181_raw leaf00181_rectangular
    leaf00181_transform leaf00181_sign leaf00181_log
#print axioms leaf00181_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
