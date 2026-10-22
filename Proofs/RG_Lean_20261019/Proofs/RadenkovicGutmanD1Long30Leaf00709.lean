/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00709 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7664814441254364691428278272000000000000 6114179372596003979165254236534028107776 57479937509549804654101004288000000000000))
theorem leaf00709_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7664814441254364691428278272000000000000 6114179372596003979165254236534028107776 57479937509549804654101004288000000000000 raw00709=true := by decide +kernel
#print axioms leaf00709_raw
theorem leaf00709_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00709=true := by decide +kernel
#print axioms leaf00709_rectangular
def affine00709 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00709 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00709_transform : affine00709=(NestedInteger.clearedAll 3 raw00709 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00709_transform
theorem leaf00709_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00709=true := by decide +kernel
#print axioms leaf00709_sign
theorem leaf00709_log : RationalLog.accepts (387084473/536870912) (-702473575/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00709_log
def leaf00709 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (53185334201/500000000000) (387084473/536870912) (-702473575/4294967296) 1 8 ![60,0,4] ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)] affine00709
theorem leaf00709_checked : FastNestedCellData.accepts 1 2 4 leaf00709=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (53185334201/500000000000) (387084473/536870912) (-702473575/4294967296) 1 8 ![60,0,4] ![(47/1600),0,(1/2)] ![(3/6400),1,(1/2)] 7664814441254364691428278272000000000000 6114179372596003979165254236534028107776 57479937509549804654101004288000000000000 raw00709 affine00709
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00709_raw leaf00709_rectangular
    leaf00709_transform leaf00709_sign leaf00709_log
#print axioms leaf00709_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
