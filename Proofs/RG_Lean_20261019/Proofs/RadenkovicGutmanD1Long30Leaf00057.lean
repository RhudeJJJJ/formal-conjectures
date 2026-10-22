/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00057 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6165492814800066551216498278400000000000 5790064865130791961810806090018605498368 216543608000111009175441506304000000000000))
theorem leaf00057_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6165492814800066551216498278400000000000 5790064865130791961810806090018605498368 216543608000111009175441506304000000000000 raw00057=true := by decide +kernel
#print axioms leaf00057_raw
theorem leaf00057_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00057=true := by decide +kernel
#print axioms leaf00057_rectangular
def affine00057 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00057 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00057_transform : affine00057=(NestedInteger.clearedAll 3 raw00057 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00057_transform
theorem leaf00057_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00057=true := by decide +kernel
#print axioms leaf00057_sign
theorem leaf00057_log : RationalLog.accepts (982099815/1073741824) (-47895289/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00057_log
def leaf00057 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26738562817/1000000000000) (982099815/1073741824) (-47895289/1073741824) 1 8 ![60,0,4] ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00057
theorem leaf00057_checked : FastNestedCellData.accepts 1 2 4 leaf00057=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26738562817/1000000000000) (982099815/1073741824) (-47895289/1073741824) 1 8 ![60,0,4] ![(27/16000),0,(1/8)] ![(1/16000),1,(1/8)] 6165492814800066551216498278400000000000 5790064865130791961810806090018605498368 216543608000111009175441506304000000000000 raw00057 affine00057
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00057_raw leaf00057_rectangular
    leaf00057_transform leaf00057_sign leaf00057_log
#print axioms leaf00057_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
