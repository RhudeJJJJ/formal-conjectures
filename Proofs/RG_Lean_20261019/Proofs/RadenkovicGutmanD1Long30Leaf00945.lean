/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00945 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 524214132579225006628575117312000000000000 141247772003894315399512173787279710486528 177514801899593569399910432768000000000000))
theorem leaf00945_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 524214132579225006628575117312000000000000 141247772003894315399512173787279710486528 177514801899593569399910432768000000000000 raw00945=true := by decide +kernel
#print axioms leaf00945_raw
theorem leaf00945_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00945=true := by decide +kernel
#print axioms leaf00945_rectangular
def affine00945 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00945 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/320),1,(1/16)]))
theorem leaf00945_transform : affine00945=(NestedInteger.clearedAll 3 raw00945 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00945_transform
theorem leaf00945_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00945=true := by decide +kernel
#print axioms leaf00945_sign
theorem leaf00945_log : RationalLog.accepts (644465969/4294967296) (-2036649065/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00945_log
def leaf00945 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (397847870973/500000000000) (644465969/4294967296) (-2036649065/2147483648) 3 8 ![60,0,4] ![(3/32),0,0] ![(1/320),1,(1/16)] affine00945
theorem leaf00945_checked : FastNestedCellData.accepts 1 2 4 leaf00945=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (397847870973/500000000000) (644465969/4294967296) (-2036649065/2147483648) 3 8 ![60,0,4] ![(3/32),0,0] ![(1/320),1,(1/16)] 524214132579225006628575117312000000000000 141247772003894315399512173787279710486528 177514801899593569399910432768000000000000 raw00945 affine00945
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00945_raw leaf00945_rectangular
    leaf00945_transform leaf00945_sign leaf00945_log
#print axioms leaf00945_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
