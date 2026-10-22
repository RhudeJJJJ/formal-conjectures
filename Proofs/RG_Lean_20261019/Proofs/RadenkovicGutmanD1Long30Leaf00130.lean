/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00130 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12572536844536018523356816998400000000000 1882319587408272544981957638201802752 6904467277210906013152051200000000000))
theorem leaf00130_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12572536844536018523356816998400000000000 1882319587408272544981957638201802752 6904467277210906013152051200000000000 raw00130=true := by decide +kernel
#print axioms leaf00130_raw
theorem leaf00130_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00130=true := by decide +kernel
#print axioms leaf00130_rectangular
def affine00130 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00130 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00130_transform : affine00130=(NestedInteger.clearedAll 3 raw00130 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00130_transform
theorem leaf00130_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00130=true := by decide +kernel
#print axioms leaf00130_sign
theorem leaf00130_log : RationalLog.accepts (252639/2147483648) (-19430101241/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00130_log
def leaf00130 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27262343521/100000000000) (252639/2147483648) (-19430101241/4294967296) 14 8 ![60,0,4] ![(47/16000),0,0] ![(3/32000),1,(1/16)] affine00130
theorem leaf00130_checked : FastNestedCellData.accepts 1 2 4 leaf00130=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27262343521/100000000000) (252639/2147483648) (-19430101241/4294967296) 14 8 ![60,0,4] ![(47/16000),0,0] ![(3/32000),1,(1/16)] 12572536844536018523356816998400000000000 1882319587408272544981957638201802752 6904467277210906013152051200000000000 raw00130 affine00130
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00130_raw leaf00130_rectangular
    leaf00130_transform leaf00130_sign leaf00130_log
#print axioms leaf00130_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
