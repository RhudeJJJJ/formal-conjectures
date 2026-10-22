/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00811 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40383942043185112781100050022400000000000 10121497412387631942360752222278860668928 14447935782353221266740084736000000000000))
theorem leaf00811_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40383942043185112781100050022400000000000 10121497412387631942360752222278860668928 14447935782353221266740084736000000000000 raw00811=true := by decide +kernel
#print axioms leaf00811_raw
theorem leaf00811_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00811=true := by decide +kernel
#print axioms leaf00811_rectangular
def affine00811 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00811 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00811_transform : affine00811=(NestedInteger.clearedAll 3 raw00811 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00811_transform
theorem leaf00811_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00811=true := by decide +kernel
#print axioms leaf00811_sign
theorem leaf00811_log : RationalLog.accepts (316502095/2147483648) (-4111834675/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00811_log
def leaf00811 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (175137430787/250000000000) (316502095/2147483648) (-4111834675/4294967296) 3 8 ![60,0,4] ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)] affine00811
theorem leaf00811_checked : FastNestedCellData.accepts 1 2 4 leaf00811=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (175137430787/250000000000) (316502095/2147483648) (-4111834675/4294967296) 3 8 ![60,0,4] ![(71/1600),0,(1/16)] ![(3/3200),1,(1/16)] 40383942043185112781100050022400000000000 10121497412387631942360752222278860668928 14447935782353221266740084736000000000000 raw00811 affine00811
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00811_raw leaf00811_rectangular
    leaf00811_transform leaf00811_sign leaf00811_log
#print axioms leaf00811_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
