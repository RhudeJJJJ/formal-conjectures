/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00287 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 73772982436141891364241958502400000000000 58825437164391684102310245521745701240832 588365956512556253818635105075200000000000))
theorem leaf00287_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 73772982436141891364241958502400000000000 58825437164391684102310245521745701240832 588365956512556253818635105075200000000000 raw00287=true := by decide +kernel
#print axioms leaf00287_raw
theorem leaf00287_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00287=true := by decide +kernel
#print axioms leaf00287_rectangular
def affine00287 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00287 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00287_transform : affine00287=(NestedInteger.clearedAll 3 raw00287 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00287_transform
theorem leaf00287_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00287=true := by decide +kernel
#print axioms leaf00287_sign
theorem leaf00287_log : RationalLog.accepts (3113454233/4294967296) (-172717365/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00287_log
def leaf00287 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19996206957/200000000000) (3113454233/4294967296) (-172717365/1073741824) 1 8 ![60,0,4] ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00287
theorem leaf00287_checked : FastNestedCellData.accepts 1 2 4 leaf00287=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19996206957/200000000000) (3113454233/4294967296) (-172717365/1073741824) 1 8 ![60,0,4] ![(41/6400),0,(1/8)] ![(1/6400),1,(1/8)] 73772982436141891364241958502400000000000 58825437164391684102310245521745701240832 588365956512556253818635105075200000000000 raw00287 affine00287
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00287_raw leaf00287_rectangular
    leaf00287_transform leaf00287_sign leaf00287_log
#print axioms leaf00287_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
