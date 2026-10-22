/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00140 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 296184006063955156671517425664000000000000 255559145194374142610498439188762064846848 3979143075401793621308922134528000000000000))
theorem leaf00140_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 296184006063955156671517425664000000000000 255559145194374142610498439188762064846848 3979143075401793621308922134528000000000000 raw00140=true := by decide +kernel
#print axioms leaf00140_raw
theorem leaf00140_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00140=true := by decide +kernel
#print axioms leaf00140_rectangular
def affine00140 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00140 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00140_transform : affine00140=(NestedInteger.clearedAll 3 raw00140 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00140_transform
theorem leaf00140_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00140=true := by decide +kernel
#print axioms leaf00140_sign
theorem leaf00140_log : RationalLog.accepts (3482221267/4294967296) (-112621329/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00140_log
def leaf00140 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (32112334283/500000000000) (3482221267/4294967296) (-112621329/1073741824) 1 8 ![52,0,4] ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)] affine00140
theorem leaf00140_checked : FastNestedCellData.accepts 1 0 4 leaf00140=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (32112334283/500000000000) (3482221267/4294967296) (-112621329/1073741824) 1 8 ![52,0,4] ![(7/400),0,(1/2)] ![(1/1600),1,(1/2)] 296184006063955156671517425664000000000000 255559145194374142610498439188762064846848 3979143075401793621308922134528000000000000 raw00140 affine00140
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00140_raw leaf00140_rectangular
    leaf00140_transform leaf00140_sign leaf00140_log
#print axioms leaf00140_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
