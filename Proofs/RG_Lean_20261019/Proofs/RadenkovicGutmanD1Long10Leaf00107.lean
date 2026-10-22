/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00107 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 76244955689853327412329185280000000000 69216365600810571476897888570443825152 1674624334682884110806354493440000000000))
theorem leaf00107_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 76244955689853327412329185280000000000 69216365600810571476897888570443825152 1674624334682884110806354493440000000000 raw00107=true := by decide +kernel
#print axioms leaf00107_raw
theorem leaf00107_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00107=true := by decide +kernel
#print axioms leaf00107_rectangular
def affine00107 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00107 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00107_transform : affine00107=(NestedInteger.clearedAll 3 raw00107 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00107_transform
theorem leaf00107_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00107=true := by decide +kernel
#print axioms leaf00107_sign
theorem leaf00107_log : RationalLog.accepts (3744278333/4294967296) (-294667099/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00107_log
def leaf00107 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (413324733/10000000000) (3744278333/4294967296) (-294667099/4294967296) 1 8 ![52,0,4] ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)] affine00107
theorem leaf00107_checked : FastNestedCellData.accepts 1 0 4 leaf00107=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (413324733/10000000000) (3744278333/4294967296) (-294667099/4294967296) 1 8 ![52,0,4] ![(9/800),0,(1/2)] ![(1/3200),1,(1/2)] 76244955689853327412329185280000000000 69216365600810571476897888570443825152 1674624334682884110806354493440000000000 raw00107 affine00107
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00107_raw leaf00107_rectangular
    leaf00107_transform leaf00107_sign leaf00107_log
#print axioms leaf00107_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
