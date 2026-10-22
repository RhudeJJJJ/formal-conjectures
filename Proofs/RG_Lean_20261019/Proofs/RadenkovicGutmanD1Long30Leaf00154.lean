/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00154 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3573879931790862937420201984000000000000 3469995268579039723219737054940971925504 279852166439743756633913688064000000000000))
theorem leaf00154_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3573879931790862937420201984000000000000 3469995268579039723219737054940971925504 279852166439743756633913688064000000000000 raw00154=true := by decide +kernel
#print axioms leaf00154_raw
theorem leaf00154_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00154=true := by decide +kernel
#print axioms leaf00154_rectangular
def affine00154 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00154 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00154_transform : affine00154=(NestedInteger.clearedAll 3 raw00154 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00154_transform
theorem leaf00154_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00154=true := by decide +kernel
#print axioms leaf00154_sign
theorem leaf00154_log : RationalLog.accepts (2059524283/2147483648) (-11226441/536870912) 1 8=true := by decide +kernel
#print axioms leaf00154_log
def leaf00154 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3099846709/250000000000) (2059524283/2147483648) (-11226441/536870912) 1 8 ![60,0,4] ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00154
theorem leaf00154_checked : FastNestedCellData.accepts 1 2 4 leaf00154=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3099846709/250000000000) (2059524283/2147483648) (-11226441/536870912) 1 8 ![60,0,4] ![(53/16000),0,(1/2)] ![(3/32000),1,(1/2)] 3573879931790862937420201984000000000000 3469995268579039723219737054940971925504 279852166439743756633913688064000000000000 raw00154 affine00154
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00154_raw leaf00154_rectangular
    leaf00154_transform leaf00154_sign leaf00154_log
#print axioms leaf00154_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
