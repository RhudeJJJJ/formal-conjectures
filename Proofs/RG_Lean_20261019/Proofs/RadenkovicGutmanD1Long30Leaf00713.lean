/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00713 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 61571865271412301137337909248000000000000 39777648765266344505705522500757606105088 186207233052051567259643019264000000000000))
theorem leaf00713_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 61571865271412301137337909248000000000000 39777648765266344505705522500757606105088 186207233052051567259643019264000000000000 raw00713=true := by decide +kernel
#print axioms leaf00713_raw
theorem leaf00713_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00713=true := by decide +kernel
#print axioms leaf00713_rectangular
def affine00713 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00713 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00713_transform : affine00713=(NestedInteger.clearedAll 3 raw00713 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00713_transform
theorem leaf00713_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00713=true := by decide +kernel
#print axioms leaf00713_sign
theorem leaf00713_log : RationalLog.accepts (1143151589/2147483648) (-677002571/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00713_log
def leaf00713 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (53405080073/250000000000) (1143151589/2147483648) (-677002571/2147483648) 1 8 ![60,0,4] ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00713
theorem leaf00713_checked : FastNestedCellData.accepts 1 2 4 leaf00713=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (53405080073/250000000000) (1143151589/2147483648) (-677002571/2147483648) 1 8 ![60,0,4] ![(191/6400),0,(1/4)] ![(3/6400),1,(1/4)] 61571865271412301137337909248000000000000 39777648765266344505705522500757606105088 186207233052051567259643019264000000000000 raw00713 affine00713
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00713_raw leaf00713_rectangular
    leaf00713_transform leaf00713_sign leaf00713_log
#print axioms leaf00713_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
