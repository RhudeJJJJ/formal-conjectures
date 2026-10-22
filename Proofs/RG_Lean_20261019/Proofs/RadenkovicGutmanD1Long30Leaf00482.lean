/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00482 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 72640398052516320413197795328000000000000 48151223694411659454226559327540405600256 254746131898887094213892112384000000000000))
theorem leaf00482_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 72640398052516320413197795328000000000000 48151223694411659454226559327540405600256 254746131898887094213892112384000000000000 raw00482=true := by decide +kernel
#print axioms leaf00482_raw
theorem leaf00482_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00482=true := by decide +kernel
#print axioms leaf00482_rectangular
def affine00482 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00482 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00482_transform : affine00482=(NestedInteger.clearedAll 3 raw00482 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00482_transform
theorem leaf00482_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00482=true := by decide +kernel
#print axioms leaf00482_sign
theorem leaf00482_log : RationalLog.accepts (598606047/1073741824) (-627388613/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00482_log
def leaf00482 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (189016505709/1000000000000) (598606047/1073741824) (-627388613/2147483648) 1 8 ![60,0,4] ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)] affine00482
theorem leaf00482_checked : FastNestedCellData.accepts 1 2 4 leaf00482=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (189016505709/1000000000000) (598606047/1073741824) (-627388613/2147483648) 1 8 ![60,0,4] ![(1/80),0,(1/8)] ![(1/6400),1,(1/8)] 72640398052516320413197795328000000000000 48151223694411659454226559327540405600256 254746131898887094213892112384000000000000 raw00482 affine00482
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00482_raw leaf00482_rectangular
    leaf00482_transform leaf00482_sign leaf00482_log
#print axioms leaf00482_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
