/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00248 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 183505684289393931053596409856000000000000 167250231926824196117858098527304471805952 4203169831727398863340168019968000000000000))
theorem leaf00248_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 183505684289393931053596409856000000000000 167250231926824196117858098527304471805952 4203169831727398863340168019968000000000000 raw00248=true := by decide +kernel
#print axioms leaf00248_raw
theorem leaf00248_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00248=true := by decide +kernel
#print axioms leaf00248_rectangular
def affine00248 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00248 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00248_transform : affine00248=(NestedInteger.clearedAll 3 raw00248 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00248_transform
theorem leaf00248_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00248=true := by decide +kernel
#print axioms leaf00248_sign
theorem leaf00248_log : RationalLog.accepts (3764703913/4294967296) (-141492051/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00248_log
def leaf00248 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19895726157/500000000000) (3764703913/4294967296) (-141492051/2147483648) 1 8 ![60,0,4] ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00248
theorem leaf00248_checked : FastNestedCellData.accepts 1 2 4 leaf00248=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19895726157/500000000000) (3764703913/4294967296) (-141492051/2147483648) 1 8 ![60,0,4] ![(33/6400),0,(1/4)] ![(1/6400),1,(1/4)] 183505684289393931053596409856000000000000 167250231926824196117858098527304471805952 4203169831727398863340168019968000000000000 raw00248 affine00248
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00248_raw leaf00248_rectangular
    leaf00248_transform leaf00248_sign leaf00248_log
#print axioms leaf00248_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
