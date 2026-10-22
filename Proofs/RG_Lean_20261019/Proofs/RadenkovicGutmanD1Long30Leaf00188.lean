/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00188 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3522726246936259400260648960000000000 3280776037145066964949274829476855808 107373578867021739700235796480000000000))
theorem leaf00188_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3522726246936259400260648960000000000 3280776037145066964949274829476855808 107373578867021739700235796480000000000 raw00188=true := by decide +kernel
#print axioms leaf00188_raw
theorem leaf00188_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00188=true := by decide +kernel
#print axioms leaf00188_rectangular
def affine00188 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00188 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00188_transform : affine00188=(NestedInteger.clearedAll 3 raw00188 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00188_transform
theorem leaf00188_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00188=true := by decide +kernel
#print axioms leaf00188_sign
theorem leaf00188_log : RationalLog.accepts (3881382723/4294967296) (-217438079/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00188_log
def leaf00188 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76386949/2500000000) (3881382723/4294967296) (-217438079/4294967296) 1 8 ![60,0,4] ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00188
theorem leaf00188_checked : FastNestedCellData.accepts 1 2 4 leaf00188=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76386949/2500000000) (3881382723/4294967296) (-217438079/4294967296) 1 8 ![60,0,4] ![(127/32000),0,(1/4)] ![(3/32000),1,(1/4)] 3522726246936259400260648960000000000 3280776037145066964949274829476855808 107373578867021739700235796480000000000 raw00188 affine00188
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00188_raw leaf00188_rectangular
    leaf00188_transform leaf00188_sign leaf00188_log
#print axioms leaf00188_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
