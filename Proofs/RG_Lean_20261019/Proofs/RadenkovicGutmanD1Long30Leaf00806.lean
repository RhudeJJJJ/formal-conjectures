/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00806 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12866987126800388569615959064576000000000000 3222746421499955926877034765911332457807872 4620287396421457449647972810752000000000000))
theorem leaf00806_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12866987126800388569615959064576000000000000 3222746421499955926877034765911332457807872 4620287396421457449647972810752000000000000 raw00806=true := by decide +kernel
#print axioms leaf00806_raw
theorem leaf00806_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00806=true := by decide +kernel
#print axioms leaf00806_rectangular
def affine00806 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00806 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00806_transform : affine00806=(NestedInteger.clearedAll 3 raw00806 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00806_transform
theorem leaf00806_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00806=true := by decide +kernel
#print axioms leaf00806_sign
theorem leaf00806_log : RationalLog.accepts (633715067/4294967296) (-4109424359/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00806_log
def leaf00806 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (697520769811/1000000000000) (633715067/4294967296) (-4109424359/4294967296) 3 8 ![60,0,4] ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00806
theorem leaf00806_checked : FastNestedCellData.accepts 1 2 4 leaf00806=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (697520769811/1000000000000) (633715067/4294967296) (-4109424359/4294967296) 3 8 ![60,0,4] ![(139/3200),0,(1/16)] ![(3/3200),1,(1/16)] 12866987126800388569615959064576000000000000 3222746421499955926877034765911332457807872 4620287396421457449647972810752000000000000 raw00806 affine00806
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00806_raw leaf00806_rectangular
    leaf00806_transform leaf00806_sign leaf00806_log
#print axioms leaf00806_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
