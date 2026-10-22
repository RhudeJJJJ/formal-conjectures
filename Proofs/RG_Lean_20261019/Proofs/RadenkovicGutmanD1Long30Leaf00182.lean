/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00182 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5395562215891254108483485696000000000000 4692443314451552361923736885947334131712 77129180639001542735003910144000000000000))
theorem leaf00182_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5395562215891254108483485696000000000000 4692443314451552361923736885947334131712 77129180639001542735003910144000000000000 raw00182=true := by decide +kernel
#print axioms leaf00182_raw
theorem leaf00182_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00182=true := by decide +kernel
#print axioms leaf00182_rectangular
def affine00182 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00182 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00182_transform : affine00182=(NestedInteger.clearedAll 3 raw00182 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00182_transform
theorem leaf00182_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00182=true := by decide +kernel
#print axioms leaf00182_sign
theorem leaf00182_log : RationalLog.accepts (880263761/1073741824) (-426669105/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00182_log
def leaf00182 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (60838754873/1000000000000) (880263761/1073741824) (-426669105/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)] affine00182
theorem leaf00182_checked : FastNestedCellData.accepts 1 2 4 leaf00182=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (60838754873/1000000000000) (880263761/1073741824) (-426669105/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/8)] ![(3/32000),1,(1/8)] 5395562215891254108483485696000000000000 4692443314451552361923736885947334131712 77129180639001542735003910144000000000000 raw00182 affine00182
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00182_raw leaf00182_rectangular
    leaf00182_transform leaf00182_sign leaf00182_log
#print axioms leaf00182_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
