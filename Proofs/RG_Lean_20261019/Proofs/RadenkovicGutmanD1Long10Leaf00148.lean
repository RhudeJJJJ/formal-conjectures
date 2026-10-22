/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00148 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2677120221522897172428482412544000000000000 1947310444200415266467542330919138881437696 13417976939336898987957361311744000000000000))
theorem leaf00148_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2677120221522897172428482412544000000000000 1947310444200415266467542330919138881437696 13417976939336898987957361311744000000000000 raw00148=true := by decide +kernel
#print axioms leaf00148_raw
theorem leaf00148_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00148=true := by decide +kernel
#print axioms leaf00148_rectangular
def affine00148 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00148 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00148_transform : affine00148=(NestedInteger.clearedAll 3 raw00148 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00148_transform
theorem leaf00148_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00148=true := by decide +kernel
#print axioms leaf00148_sign
theorem leaf00148_log : RationalLog.accepts (2728183221/4294967296) (-974545381/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00148_log
def leaf00148 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (145126978009/1000000000000) (2728183221/4294967296) (-974545381/4294967296) 1 8 ![52,0,4] ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00148
theorem leaf00148_checked : FastNestedCellData.accepts 1 0 4 leaf00148=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (145126978009/1000000000000) (2728183221/4294967296) (-974545381/4294967296) 1 8 ![52,0,4] ![(31/1600),0,(1/4)] ![(1/1600),1,(1/4)] 2677120221522897172428482412544000000000000 1947310444200415266467542330919138881437696 13417976939336898987957361311744000000000000 raw00148 affine00148
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00148_raw leaf00148_rectangular
    leaf00148_transform leaf00148_sign leaf00148_log
#print axioms leaf00148_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
