/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00153 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 30085650438674165755153481728000000000000 236740467877131154684714684030851743744 567012787754480102725910528000000000000))
theorem leaf00153_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 30085650438674165755153481728000000000000 236740467877131154684714684030851743744 567012787754480102725910528000000000000 raw00153=true := by decide +kernel
#print axioms leaf00153_raw
theorem leaf00153_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00153=true := by decide +kernel
#print axioms leaf00153_rectangular
def affine00153 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00153 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00153_transform : affine00153=(NestedInteger.clearedAll 3 raw00153 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(131/6400),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00153_transform
theorem leaf00153_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00153=true := by decide +kernel
#print axioms leaf00153_sign
theorem leaf00153_log : RationalLog.accepts (23842021/4294967296) (-11153492637/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00153_log
def leaf00153 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (26095142053/62500000000) (23842021/4294967296) (-11153492637/4294967296) 8 8 ![52,0,4] ![(131/6400),0,0] ![(3/6400),1,(1/4)] affine00153
theorem leaf00153_checked : FastNestedCellData.accepts 1 0 4 leaf00153=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (26095142053/62500000000) (23842021/4294967296) (-11153492637/4294967296) 8 8 ![52,0,4] ![(131/6400),0,0] ![(3/6400),1,(1/4)] 30085650438674165755153481728000000000000 236740467877131154684714684030851743744 567012787754480102725910528000000000000 raw00153 affine00153
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00153_raw leaf00153_rectangular
    leaf00153_transform leaf00153_sign leaf00153_log
#print axioms leaf00153_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
