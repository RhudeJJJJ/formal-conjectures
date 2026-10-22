/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00667 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 405022894618043237777618763776000000000000 197017425745466240717916981639120584441856 560821696606658070237262381056000000000000))
theorem leaf00667_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 405022894618043237777618763776000000000000 197017425745466240717916981639120584441856 560821696606658070237262381056000000000000 raw00667=true := by decide +kernel
#print axioms leaf00667_raw
theorem leaf00667_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00667=true := by decide +kernel
#print axioms leaf00667_rectangular
def affine00667 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00667 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00667_transform : affine00667=(NestedInteger.clearedAll 3 raw00667 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00667_transform
theorem leaf00667_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00667=true := by decide +kernel
#print axioms leaf00667_sign
theorem leaf00667_log : RationalLog.accepts (386520669/1073741824) (-1097063011/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00667_log
def leaf00667 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (351301361801/1000000000000) (386520669/1073741824) (-1097063011/2147483648) 2 8 ![60,0,4] ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)] affine00667
theorem leaf00667_checked : FastNestedCellData.accepts 1 2 4 leaf00667=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (351301361801/1000000000000) (386520669/1073741824) (-1097063011/2147483648) 2 8 ![60,0,4] ![(41/1600),0,(1/8)] ![(3/6400),1,(1/8)] 405022894618043237777618763776000000000000 197017425745466240717916981639120584441856 560821696606658070237262381056000000000000 raw00667 affine00667
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00667_raw leaf00667_rectangular
    leaf00667_transform leaf00667_sign leaf00667_log
#print axioms leaf00667_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
