/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00826 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 204199426301956599574698131456000000000000 51414859913243035087593911236639806455808 72572801407716832235111841792000000000000))
theorem leaf00826_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 204199426301956599574698131456000000000000 51414859913243035087593911236639806455808 72572801407716832235111841792000000000000 raw00826=true := by decide +kernel
#print axioms leaf00826_raw
theorem leaf00826_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00826=true := by decide +kernel
#print axioms leaf00826_rectangular
def affine00826 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00826 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00826_transform : affine00826=(NestedInteger.clearedAll 3 raw00826 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00826_transform
theorem leaf00826_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00826=true := by decide +kernel
#print axioms leaf00826_sign
theorem leaf00826_log : RationalLog.accepts (158244793/1073741824) (-4111919551/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00826_log
def leaf00826 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (354229538587/500000000000) (158244793/1073741824) (-4111919551/4294967296) 3 8 ![60,0,4] ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00826
theorem leaf00826_checked : FastNestedCellData.accepts 1 2 4 leaf00826=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (354229538587/500000000000) (158244793/1073741824) (-4111919551/4294967296) 3 8 ![60,0,4] ![(151/3200),0,(1/16)] ![(3/3200),1,(1/16)] 204199426301956599574698131456000000000000 51414859913243035087593911236639806455808 72572801407716832235111841792000000000000 raw00826 affine00826
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00826_raw leaf00826_rectangular
    leaf00826_transform leaf00826_sign leaf00826_log
#print axioms leaf00826_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
