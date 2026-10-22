/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00177 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 219126373675640611032185333350400000000000 191176937935969794621404766001595582251008 3218774616441641485624582078464000000000000))
theorem leaf00177_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 219126373675640611032185333350400000000000 191176937935969794621404766001595582251008 3218774616441641485624582078464000000000000 raw00177=true := by decide +kernel
#print axioms leaf00177_raw
theorem leaf00177_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00177=true := by decide +kernel
#print axioms leaf00177_rectangular
def affine00177 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00177 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00177_transform : affine00177=(NestedInteger.clearedAll 3 raw00177 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00177_transform
theorem leaf00177_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00177=true := by decide +kernel
#print axioms leaf00177_sign
theorem leaf00177_log : RationalLog.accepts (3537065235/4294967296) (-416926657/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00177_log
def leaf00177 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (59394322597/1000000000000) (3537065235/4294967296) (-416926657/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00177
theorem leaf00177_checked : FastNestedCellData.accepts 1 2 4 leaf00177=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (59394322597/1000000000000) (3537065235/4294967296) (-416926657/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/8)] ![(3/32000),1,(1/8)] 219126373675640611032185333350400000000000 191176937935969794621404766001595582251008 3218774616441641485624582078464000000000000 raw00177 affine00177
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00177_raw leaf00177_rectangular
    leaf00177_transform leaf00177_sign leaf00177_log
#print axioms leaf00177_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
