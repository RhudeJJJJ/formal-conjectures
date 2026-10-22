/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00047 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5625469554739841996737740800000000000 5370909664399647353514124553031254016 286653721706963374784380928000000000000))
theorem leaf00047_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5625469554739841996737740800000000000 5370909664399647353514124553031254016 286653721706963374784380928000000000000 raw00047=true := by decide +kernel
#print axioms leaf00047_raw
theorem leaf00047_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00047=true := by decide +kernel
#print axioms leaf00047_rectangular
def affine00047 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00047 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00047_transform : affine00047=(NestedInteger.clearedAll 3 raw00047 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00047_transform
theorem leaf00047_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00047=true := by decide +kernel
#print axioms leaf00047_sign
theorem leaf00047_log : RationalLog.accepts (4025195985/4294967296) (-139308029/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00047_log
def leaf00047 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (292759023/15625000000) (4025195985/4294967296) (-139308029/4294967296) 1 8 ![52,0,4] ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)] affine00047
theorem leaf00047_checked : FastNestedCellData.accepts 1 0 4 leaf00047=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (292759023/15625000000) (4025195985/4294967296) (-139308029/4294967296) 1 8 ![52,0,4] ![(1/200),0,(1/2)] ![(1/3200),1,(1/2)] 5625469554739841996737740800000000000 5370909664399647353514124553031254016 286653721706963374784380928000000000000 raw00047 affine00047
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00047_raw leaf00047_rectangular
    leaf00047_transform leaf00047_sign leaf00047_log
#print axioms leaf00047_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
