/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00152 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15034617540881597238024863744000000000000 13327686568394716556040415454425711116288 255506606828873913826214412288000000000000))
theorem leaf00152_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15034617540881597238024863744000000000000 13327686568394716556040415454425711116288 255506606828873913826214412288000000000000 raw00152=true := by decide +kernel
#print axioms leaf00152_raw
theorem leaf00152_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00152=true := by decide +kernel
#print axioms leaf00152_rectangular
def affine00152 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00152 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00152_transform : affine00152=(NestedInteger.clearedAll 3 raw00152 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00152_transform
theorem leaf00152_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00152=true := by decide +kernel
#print axioms leaf00152_sign
theorem leaf00152_log : RationalLog.accepts (452324099/536870912) (-183995045/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00152_log
def leaf00152 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52161808001/1000000000000) (452324099/536870912) (-183995045/2147483648) 1 8 ![60,0,4] ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00152
theorem leaf00152_checked : FastNestedCellData.accepts 1 2 4 leaf00152=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52161808001/1000000000000) (452324099/536870912) (-183995045/2147483648) 1 8 ![60,0,4] ![(53/16000),0,(1/8)] ![(3/32000),1,(1/8)] 15034617540881597238024863744000000000000 13327686568394716556040415454425711116288 255506606828873913826214412288000000000000 raw00152 affine00152
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00152_raw leaf00152_rectangular
    leaf00152_transform leaf00152_sign leaf00152_log
#print axioms leaf00152_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
