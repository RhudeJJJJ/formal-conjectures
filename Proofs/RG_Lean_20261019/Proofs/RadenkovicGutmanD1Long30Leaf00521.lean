/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00521 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 469950607991252849155654025216000000000000 194008496122024358852201482236463757131776 475957607995432646647675355136000000000000))
theorem leaf00521_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 469950607991252849155654025216000000000000 194008496122024358852201482236463757131776 475957607995432646647675355136000000000000 raw00521=true := by decide +kernel
#print axioms leaf00521_raw
theorem leaf00521_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00521=true := by decide +kernel
#print axioms leaf00521_rectangular
def affine00521 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00521 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00521_transform : affine00521=(NestedInteger.clearedAll 3 raw00521 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00521_transform
theorem leaf00521_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00521=true := by decide +kernel
#print axioms leaf00521_sign
theorem leaf00521_log : RationalLog.accepts (1259632441/4294967296) (-1317077501/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00521_log
def leaf00521 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (101904294029/250000000000) (1259632441/4294967296) (-1317077501/2147483648) 2 8 ![60,0,4] ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00521
theorem leaf00521_checked : FastNestedCellData.accepts 1 2 4 leaf00521=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (101904294029/250000000000) (1259632441/4294967296) (-1317077501/2147483648) 2 8 ![60,0,4] ![(47/3200),0,(1/16)] ![(1/3200),1,(1/16)] 469950607991252849155654025216000000000000 194008496122024358852201482236463757131776 475957607995432646647675355136000000000000 raw00521 affine00521
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00521_raw leaf00521_rectangular
    leaf00521_transform leaf00521_sign leaf00521_log
#print axioms leaf00521_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
