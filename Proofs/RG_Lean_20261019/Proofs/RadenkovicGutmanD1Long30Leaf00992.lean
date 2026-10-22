/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00992 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 422022418663727086213779412746240000000000 233370541559476787368878327520263690780672 408028243439919072875949064192000000000000))
theorem leaf00992_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 422022418663727086213779412746240000000000 233370541559476787368878327520263690780672 408028243439919072875949064192000000000000 raw00992=true := by decide +kernel
#print axioms leaf00992_raw
theorem leaf00992_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00992=true := by decide +kernel
#print axioms leaf00992_rectangular
def affine00992 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00992 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00992_transform : affine00992=(NestedInteger.clearedAll 3 raw00992 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00992_transform
theorem leaf00992_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00992=true := by decide +kernel
#print axioms leaf00992_sign
theorem leaf00992_log : RationalLog.accepts (1510888675/4294967296) (-2243574887/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00992_log
def leaf00992 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (571947028941/1000000000000) (1510888675/4294967296) (-2243574887/4294967296) 2 8 ![60,0,4] ![(11/80),0,(1/8)] ![(1/160),1,(1/8)] affine00992
theorem leaf00992_checked : FastNestedCellData.accepts 1 2 4 leaf00992=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (571947028941/1000000000000) (1510888675/4294967296) (-2243574887/4294967296) 2 8 ![60,0,4] ![(11/80),0,(1/8)] ![(1/160),1,(1/8)] 422022418663727086213779412746240000000000 233370541559476787368878327520263690780672 408028243439919072875949064192000000000000 raw00992 affine00992
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00992_raw leaf00992_rectangular
    leaf00992_transform leaf00992_sign leaf00992_log
#print axioms leaf00992_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
