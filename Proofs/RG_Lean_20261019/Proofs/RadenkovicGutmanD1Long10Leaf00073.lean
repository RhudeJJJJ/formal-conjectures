/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00073 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 11089348097723670976286372659200000000000 9637719126376859136800934539759198404608 160320098721640501849954346598400000000000))
theorem leaf00073_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 11089348097723670976286372659200000000000 9637719126376859136800934539759198404608 160320098721640501849954346598400000000000 raw00073=true := by decide +kernel
#print axioms leaf00073_raw
theorem leaf00073_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00073=true := by decide +kernel
#print axioms leaf00073_rectangular
def affine00073 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00073 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00073_transform : affine00073=(NestedInteger.clearedAll 3 raw00073 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00073_transform
theorem leaf00073_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00073=true := by decide +kernel
#print axioms leaf00073_sign
theorem leaf00073_log : RationalLog.accepts (1760536121/2147483648) (-53332327/536870912) 1 8=true := by decide +kernel
#print axioms leaf00073_log
def leaf00073 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (12023095299/200000000000) (1760536121/2147483648) (-53332327/536870912) 1 8 ![52,0,4] ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)] affine00073
theorem leaf00073_checked : FastNestedCellData.accepts 1 0 4 leaf00073=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (12023095299/200000000000) (1760536121/2147483648) (-53332327/536870912) 1 8 ![52,0,4] ![(1/128),0,(1/4)] ![(1/3200),1,(1/4)] 11089348097723670976286372659200000000000 9637719126376859136800934539759198404608 160320098721640501849954346598400000000000 raw00073 affine00073
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00073_raw leaf00073_rectangular
    leaf00073_transform leaf00073_sign leaf00073_log
#print axioms leaf00073_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
