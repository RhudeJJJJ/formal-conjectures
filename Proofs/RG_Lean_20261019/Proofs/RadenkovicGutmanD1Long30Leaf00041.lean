/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00041 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 889293416235882714394565541888000000000000 794587293911163014470530201256229483839488 16482241054973446767108545314816000000000000))
theorem leaf00041_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 889293416235882714394565541888000000000000 794587293911163014470530201256229483839488 16482241054973446767108545314816000000000000 raw00041=true := by decide +kernel
#print axioms leaf00041_raw
theorem leaf00041_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00041=true := by decide +kernel
#print axioms leaf00041_rectangular
def affine00041 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00041 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00041_transform : affine00041=(NestedInteger.clearedAll 3 raw00041 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00041_transform
theorem leaf00041_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00041=true := by decide +kernel
#print axioms leaf00041_sign
theorem leaf00041_log : RationalLog.accepts (3661075147/4294967296) (-171462715/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00041_log
def leaf00041 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48208692693/1000000000000) (3661075147/4294967296) (-171462715/2147483648) 1 8 ![60,0,4] ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)] affine00041
theorem leaf00041_checked : FastNestedCellData.accepts 1 2 4 leaf00041=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48208692693/1000000000000) (3661075147/4294967296) (-171462715/2147483648) 1 8 ![60,0,4] ![(3/2000),0,(1/16)] ![(1/16000),1,(1/16)] 889293416235882714394565541888000000000000 794587293911163014470530201256229483839488 16482241054973446767108545314816000000000000 raw00041 affine00041
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00041_raw leaf00041_rectangular
    leaf00041_transform leaf00041_sign leaf00041_log
#print axioms leaf00041_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
