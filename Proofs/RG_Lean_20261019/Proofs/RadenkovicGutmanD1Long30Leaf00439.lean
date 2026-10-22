/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00439 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 757915762459871309611795480576000000000000 690000718693494727892605329059510145253376 16793774847885509561123304636416000000000000))
theorem leaf00439_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 757915762459871309611795480576000000000000 690000718693494727892605329059510145253376 16793774847885509561123304636416000000000000 raw00439=true := by decide +kernel
#print axioms leaf00439_raw
theorem leaf00439_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00439=true := by decide +kernel
#print axioms leaf00439_rectangular
def affine00439 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00439 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00439_transform : affine00439=(NestedInteger.clearedAll 3 raw00439 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00439_transform
theorem leaf00439_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00439=true := by decide +kernel
#print axioms leaf00439_sign
theorem leaf00439_log : RationalLog.accepts (3755792311/4294967296) (-288073535/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00439_log
def leaf00439 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (41086695811/1000000000000) (3755792311/4294967296) (-288073535/4294967296) 1 8 ![60,0,4] ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00439
theorem leaf00439_checked : FastNestedCellData.accepts 1 2 4 leaf00439=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (41086695811/1000000000000) (3755792311/4294967296) (-288073535/4294967296) 1 8 ![60,0,4] ![(71/6400),0,(1/2)] ![(1/6400),1,(1/2)] 757915762459871309611795480576000000000000 690000718693494727892605329059510145253376 16793774847885509561123304636416000000000000 raw00439 affine00439
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00439_raw leaf00439_rectangular
    leaf00439_transform leaf00439_sign leaf00439_log
#print axioms leaf00439_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
