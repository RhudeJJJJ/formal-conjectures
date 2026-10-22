/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00034 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5985945942279293555311640576000000000000 5910802392437724411509407552897309212672 1138448501445737025824171753472000000000000))
theorem leaf00034_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5985945942279293555311640576000000000000 5910802392437724411509407552897309212672 1138448501445737025824171753472000000000000 raw00034=true := by decide +kernel
#print axioms leaf00034_raw
theorem leaf00034_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00034=true := by decide +kernel
#print axioms leaf00034_rectangular
def affine00034 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00034 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00034_transform : affine00034=(NestedInteger.clearedAll 3 raw00034 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00034_transform
theorem leaf00034_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00034=true := by decide +kernel
#print axioms leaf00034_sign
theorem leaf00034_log : RationalLog.accepts (4219145437/4294967296) (-38249591/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00034_log
def leaf00034 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1297995119/250000000000) (4219145437/4294967296) (-38249591/4294967296) 1 8 ![60,0,4] ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)] affine00034
theorem leaf00034_checked : FastNestedCellData.accepts 1 2 4 leaf00034=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1297995119/250000000000) (4219145437/4294967296) (-38249591/4294967296) 1 8 ![60,0,4] ![(11/8000),0,(1/2)] ![(1/16000),1,(1/2)] 5985945942279293555311640576000000000000 5910802392437724411509407552897309212672 1138448501445737025824171753472000000000000 raw00034 affine00034
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00034_raw leaf00034_rectangular
    leaf00034_transform leaf00034_sign leaf00034_log
#print axioms leaf00034_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
