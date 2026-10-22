/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00178 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1343458362715533287086253670400000000000 1255180266635568374285256145612031655936 43086540282118740176853899673600000000000))
theorem leaf00178_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1343458362715533287086253670400000000000 1255180266635568374285256145612031655936 43086540282118740176853899673600000000000 raw00178=true := by decide +kernel
#print axioms leaf00178_raw
theorem leaf00178_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00178=true := by decide +kernel
#print axioms leaf00178_rectangular
def affine00178 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00178 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00178_transform : affine00178=(NestedInteger.clearedAll 3 raw00178 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00178_transform
theorem leaf00178_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00178=true := by decide +kernel
#print axioms leaf00178_sign
theorem leaf00178_log : RationalLog.accepts (1949579007/2147483648) (-51906463/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00178_log
def leaf00178 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2913160951/100000000000) (1949579007/2147483648) (-51906463/1073741824) 1 8 ![60,0,4] ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00178
theorem leaf00178_checked : FastNestedCellData.accepts 1 2 4 leaf00178=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2913160951/100000000000) (1949579007/2147483648) (-51906463/1073741824) 1 8 ![60,0,4] ![(121/32000),0,(1/4)] ![(3/32000),1,(1/4)] 1343458362715533287086253670400000000000 1255180266635568374285256145612031655936 43086540282118740176853899673600000000000 raw00178 affine00178
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00178_raw leaf00178_rectangular
    leaf00178_transform leaf00178_sign leaf00178_log
#print axioms leaf00178_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
