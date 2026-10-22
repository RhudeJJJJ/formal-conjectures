/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00638 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7949728162083382847304053555200000000 5557601704562890089689442066651676672 33013747740386852128345921945600000000))
theorem leaf00638_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7949728162083382847304053555200000000 5557601704562890089689442066651676672 33013747740386852128345921945600000000 raw00638=true := by decide +kernel
#print axioms leaf00638_raw
theorem leaf00638_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00638=true := by decide +kernel
#print axioms leaf00638_rectangular
def affine00638 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00638 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00638_transform : affine00638=(NestedInteger.clearedAll 3 raw00638 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00638_transform
theorem leaf00638_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00638=true := by decide +kernel
#print axioms leaf00638_sign
theorem leaf00638_log : RationalLog.accepts (2569951913/4294967296) (-1102854765/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00638_log
def leaf00638 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (269347267/1600000000) (2569951913/4294967296) (-1102854765/4294967296) 1 8 ![60,0,4] ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00638
theorem leaf00638_checked : FastNestedCellData.accepts 1 2 4 leaf00638=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (269347267/1600000000) (2569951913/4294967296) (-1102854765/4294967296) 1 8 ![60,0,4] ![(73/3200),0,(1/4)] ![(3/6400),1,(1/4)] 7949728162083382847304053555200000000 5557601704562890089689442066651676672 33013747740386852128345921945600000000 raw00638 affine00638
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00638_raw leaf00638_rectangular
    leaf00638_transform leaf00638_sign leaf00638_log
#print axioms leaf00638_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
