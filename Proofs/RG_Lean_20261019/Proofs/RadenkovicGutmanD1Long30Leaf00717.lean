/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00717 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 456922304690478147350426550272000000000000 206448703041518863127299990043640729698304 520918210582859689634700460032000000000000))
theorem leaf00717_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 456922304690478147350426550272000000000000 206448703041518863127299990043640729698304 520918210582859689634700460032000000000000 raw00717=true := by decide +kernel
#print axioms leaf00717_raw
theorem leaf00717_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00717=true := by decide +kernel
#print axioms leaf00717_rectangular
def affine00717 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00717 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00717_transform : affine00717=(NestedInteger.clearedAll 3 raw00717 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00717_transform
theorem leaf00717_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00717=true := by decide +kernel
#print axioms leaf00717_sign
theorem leaf00717_log : RationalLog.accepts (694889363/2147483648) (-2423004575/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00717_log
def leaf00717 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (198158462161/500000000000) (694889363/2147483648) (-2423004575/4294967296) 2 8 ![60,0,4] ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00717
theorem leaf00717_checked : FastNestedCellData.accepts 1 2 4 leaf00717=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (198158462161/500000000000) (694889363/2147483648) (-2423004575/4294967296) 2 8 ![60,0,4] ![(97/3200),0,(1/8)] ![(3/6400),1,(1/8)] 456922304690478147350426550272000000000000 206448703041518863127299990043640729698304 520918210582859689634700460032000000000000 raw00717 affine00717
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00717_raw leaf00717_rectangular
    leaf00717_transform leaf00717_sign leaf00717_log
#print axioms leaf00717_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
