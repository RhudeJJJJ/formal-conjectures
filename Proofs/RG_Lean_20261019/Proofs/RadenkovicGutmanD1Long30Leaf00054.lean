/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00054 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7049942103950352397040091136000000000000 6946583814109972433102287708551274037248 1136018671465906810523503034368000000000000))
theorem leaf00054_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7049942103950352397040091136000000000000 6946583814109972433102287708551274037248 1136018671465906810523503034368000000000000 raw00054=true := by decide +kernel
#print axioms leaf00054_raw
theorem leaf00054_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00054=true := by decide +kernel
#print axioms leaf00054_rectangular
def affine00054 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00054 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00054_transform : affine00054=(NestedInteger.clearedAll 3 raw00054 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00054_transform
theorem leaf00054_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00054=true := by decide +kernel
#print axioms leaf00054_sign
theorem leaf00054_log : RationalLog.accepts (4206278573/4294967296) (-11202161/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00054_log
def leaf00054 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1528712509/250000000000) (4206278573/4294967296) (-11202161/1073741824) 1 8 ![60,0,4] ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)] affine00054
theorem leaf00054_checked : FastNestedCellData.accepts 1 2 4 leaf00054=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1528712509/250000000000) (4206278573/4294967296) (-11202161/1073741824) 1 8 ![60,0,4] ![(13/8000),0,(1/2)] ![(1/16000),1,(1/2)] 7049942103950352397040091136000000000000 6946583814109972433102287708551274037248 1136018671465906810523503034368000000000000 raw00054 affine00054
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00054_raw leaf00054_rectangular
    leaf00054_transform leaf00054_sign leaf00054_log
#print axioms leaf00054_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
