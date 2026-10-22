/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00539 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1066426281889283386900161232896000000000000 935928036869737212128295558022506284580864 16189421866984592563776304185344000000000000))
theorem leaf00539_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1066426281889283386900161232896000000000000 935928036869737212128295558022506284580864 16189421866984592563776304185344000000000000 raw00539=true := by decide +kernel
#print axioms leaf00539_raw
theorem leaf00539_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00539=true := by decide +kernel
#print axioms leaf00539_rectangular
def affine00539 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00539 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00539_transform : affine00539=(NestedInteger.clearedAll 3 raw00539 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00539_transform
theorem leaf00539_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00539=true := by decide +kernel
#print axioms leaf00539_sign
theorem leaf00539_log : RationalLog.accepts (3563390069/4294967296) (-25062691/268435456) 1 8=true := by decide +kernel
#print axioms leaf00539_log
def leaf00539 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (57811084581/1000000000000) (3563390069/4294967296) (-25062691/268435456) 1 8 ![60,0,4] ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)] affine00539
theorem leaf00539_checked : FastNestedCellData.accepts 1 2 4 leaf00539=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (57811084581/1000000000000) (3563390069/4294967296) (-25062691/268435456) 1 8 ![60,0,4] ![(1/64),0,(1/2)] ![(1/3200),1,(1/2)] 1066426281889283386900161232896000000000000 935928036869737212128295558022506284580864 16189421866984592563776304185344000000000000 raw00539 affine00539
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00539_raw leaf00539_rectangular
    leaf00539_transform leaf00539_sign leaf00539_log
#print axioms leaf00539_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
