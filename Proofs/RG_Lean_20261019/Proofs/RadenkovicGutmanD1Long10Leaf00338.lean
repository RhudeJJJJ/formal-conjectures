/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00338 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 388791825143327461427613007872000000000000 261025712591003013471003180417109790294016 774044457314789909496099504128000000000000))
theorem leaf00338_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 388791825143327461427613007872000000000000 261025712591003013471003180417109790294016 774044457314789909496099504128000000000000 raw00338=true := by decide +kernel
#print axioms leaf00338_raw
theorem leaf00338_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00338=true := by decide +kernel
#print axioms leaf00338_rectangular
def affine00338 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00338 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00338_transform : affine00338=(NestedInteger.clearedAll 3 raw00338 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00338_transform
theorem leaf00338_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00338=true := by decide +kernel
#print axioms leaf00338_sign
theorem leaf00338_log : RationalLog.accepts (2156364329/4294967296) (-1479659903/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00338_log
def leaf00338 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (84305788293/250000000000) (2156364329/4294967296) (-1479659903/4294967296) 1 8 ![52,0,4] ![(21/160),0,(1/2)] ![(1/160),1,(1/2)] affine00338
theorem leaf00338_checked : FastNestedCellData.accepts 1 0 4 leaf00338=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (84305788293/250000000000) (2156364329/4294967296) (-1479659903/4294967296) 1 8 ![52,0,4] ![(21/160),0,(1/2)] ![(1/160),1,(1/2)] 388791825143327461427613007872000000000000 261025712591003013471003180417109790294016 774044457314789909496099504128000000000000 raw00338 affine00338
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00338_raw leaf00338_rectangular
    leaf00338_transform leaf00338_sign leaf00338_log
#print axioms leaf00338_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
