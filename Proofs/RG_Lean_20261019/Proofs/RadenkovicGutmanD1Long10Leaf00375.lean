/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00375 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 454984218757729203654192267264000000000000 472511507067592153483606735822279717945344 1197335325519271553567027101696000000000000))
theorem leaf00375_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 454984218757729203654192267264000000000000 472511507067592153483606735822279717945344 1197335325519271553567027101696000000000000 raw00375=true := by decide +kernel
#print axioms leaf00375_raw
theorem leaf00375_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00375=true := by decide +kernel
#print axioms leaf00375_rectangular
def affine00375 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00375 (IntegerComputedClassCell.leftNumerator ![(7/20),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,0] ![(3/80),1,(1/4)]))
theorem leaf00375_transform : affine00375=(NestedInteger.clearedAll 3 raw00375 (IntegerComputedClassCell.leftNumerator ![(7/20),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00375_transform
theorem leaf00375_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00375=true := by decide +kernel
#print axioms leaf00375_sign
theorem leaf00375_log : RationalLog.accepts (799567411/1073741824) (-633151259/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00375_log
def leaf00375 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (394635902739/1000000000000) (799567411/1073741824) (-633151259/4294967296) 1 8 ![52,0,4] ![(7/20),0,0] ![(3/80),1,(1/4)] affine00375
theorem leaf00375_checked : FastNestedCellData.accepts 1 0 4 leaf00375=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (394635902739/1000000000000) (799567411/1073741824) (-633151259/4294967296) 1 8 ![52,0,4] ![(7/20),0,0] ![(3/80),1,(1/4)] 454984218757729203654192267264000000000000 472511507067592153483606735822279717945344 1197335325519271553567027101696000000000000 raw00375 affine00375
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00375_raw leaf00375_rectangular
    leaf00375_transform leaf00375_sign leaf00375_log
#print axioms leaf00375_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
