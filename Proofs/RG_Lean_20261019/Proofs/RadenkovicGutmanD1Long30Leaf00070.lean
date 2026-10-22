/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00070 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3296535688160858348228888756224000000000000 142320632459996630841654875369827729408 796397349140401883680079872000000000000))
theorem leaf00070_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3296535688160858348228888756224000000000000 142320632459996630841654875369827729408 796397349140401883680079872000000000000 raw00070=true := by decide +kernel
#print axioms leaf00070_raw
theorem leaf00070_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00070=true := by decide +kernel
#print axioms leaf00070_rectangular
def affine00070 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00070 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/1600),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00070_transform : affine00070=(NestedInteger.clearedAll 3 raw00070 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/1600),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00070_transform
theorem leaf00070_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00070=true := by decide +kernel
#print axioms leaf00070_sign
theorem leaf00070_log : RationalLog.accepts (157313/4294967296) (-10967969179/2147483648) 15 8=true := by decide +kernel
#print axioms leaf00070_log
def leaf00070 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (178705557739/1000000000000) (157313/4294967296) (-10967969179/2147483648) 15 8 ![60,0,4] ![(3/1600),0,0] ![(1/16000),1,(1/16)] affine00070
theorem leaf00070_checked : FastNestedCellData.accepts 1 2 4 leaf00070=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (178705557739/1000000000000) (157313/4294967296) (-10967969179/2147483648) 15 8 ![60,0,4] ![(3/1600),0,0] ![(1/16000),1,(1/16)] 3296535688160858348228888756224000000000000 142320632459996630841654875369827729408 796397349140401883680079872000000000000 raw00070 affine00070
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00070_raw leaf00070_rectangular
    leaf00070_transform leaf00070_sign leaf00070_log
#print axioms leaf00070_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
