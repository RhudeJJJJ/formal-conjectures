/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00533 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1665943219435993880446841651200000000000 1290929182511324933692219419673447366656 11167397529503752789306638336000000000000))
theorem leaf00533_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1665943219435993880446841651200000000000 1290929182511324933692219419673447366656 11167397529503752789306638336000000000000 raw00533=true := by decide +kernel
#print axioms leaf00533_raw
theorem leaf00533_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00533=true := by decide +kernel
#print axioms leaf00533_rectangular
def affine00533 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00533 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00533_transform : affine00533=(NestedInteger.clearedAll 3 raw00533 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00533_transform
theorem leaf00533_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00533=true := by decide +kernel
#print axioms leaf00533_sign
theorem leaf00533_log : RationalLog.accepts (2983282255/4294967296) (-782585637/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00533_log
def leaf00533 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7224877031/62500000000) (2983282255/4294967296) (-782585637/4294967296) 1 8 ![60,0,4] ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00533
theorem leaf00533_checked : FastNestedCellData.accepts 1 2 4 leaf00533=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7224877031/62500000000) (2983282255/4294967296) (-782585637/4294967296) 1 8 ![60,0,4] ![(49/3200),0,(1/4)] ![(1/3200),1,(1/4)] 1665943219435993880446841651200000000000 1290929182511324933692219419673447366656 11167397529503752789306638336000000000000 raw00533 affine00533
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00533_raw leaf00533_rectangular
    leaf00533_transform leaf00533_sign leaf00533_log
#print axioms leaf00533_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
