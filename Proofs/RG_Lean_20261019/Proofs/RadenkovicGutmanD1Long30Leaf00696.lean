/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00696 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 27378120051385629690717798400000000000 7613347814007231942804356661419966464 12523675955051425213028761600000000000))
theorem leaf00696_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 27378120051385629690717798400000000000 7613347814007231942804356661419966464 12523675955051425213028761600000000000 raw00696=true := by decide +kernel
#print axioms leaf00696_raw
theorem leaf00696_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00696=true := by decide +kernel
#print axioms leaf00696_rectangular
def affine00696 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00696 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00696_transform : affine00696=(NestedInteger.clearedAll 3 raw00696 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00696_transform
theorem leaf00696_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00696=true := by decide +kernel
#print axioms leaf00696_sign
theorem leaf00696_log : RationalLog.accepts (92849263/536870912) (-3768362167/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00696_log
def leaf00696 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7598954813/12500000000) (92849263/536870912) (-3768362167/4294967296) 3 8 ![60,0,4] ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00696
theorem leaf00696_checked : FastNestedCellData.accepts 1 2 4 leaf00696=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7598954813/12500000000) (92849263/536870912) (-3768362167/4294967296) 3 8 ![60,0,4] ![(91/3200),0,(1/16)] ![(3/6400),1,(1/16)] 27378120051385629690717798400000000000 7613347814007231942804356661419966464 12523675955051425213028761600000000000 raw00696 affine00696
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00696_raw leaf00696_rectangular
    leaf00696_transform leaf00696_sign leaf00696_log
#print axioms leaf00696_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
