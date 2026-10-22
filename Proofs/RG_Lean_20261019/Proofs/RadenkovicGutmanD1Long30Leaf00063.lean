/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00063 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 240657153823853329029215027200000000000 233019281981280328142788351518754996224 17174316684102447158544826368000000000000))
theorem leaf00063_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 240657153823853329029215027200000000000 233019281981280328142788351518754996224 17174316684102447158544826368000000000000 raw00063=true := by decide +kernel
#print axioms leaf00063_raw
theorem leaf00063_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00063=true := by decide +kernel
#print axioms leaf00063_rectangular
def affine00063 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00063 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00063_transform : affine00063=(NestedInteger.clearedAll 3 raw00063 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00063_transform
theorem leaf00063_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00063=true := by decide +kernel
#print axioms leaf00063_sign
theorem leaf00063_log : RationalLog.accepts (4102986615/4294967296) (-98201865/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00063_log
def leaf00063 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3391973117/250000000000) (4102986615/4294967296) (-98201865/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)] affine00063
theorem leaf00063_checked : FastNestedCellData.accepts 1 2 4 leaf00063=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3391973117/250000000000) (4102986615/4294967296) (-98201865/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/4)] ![(1/16000),1,(1/4)] 240657153823853329029215027200000000000 233019281981280328142788351518754996224 17174316684102447158544826368000000000000 raw00063 affine00063
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00063_raw leaf00063_rectangular
    leaf00063_transform leaf00063_sign leaf00063_log
#print axioms leaf00063_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
