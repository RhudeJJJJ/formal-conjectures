/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00070 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9516299883302386716960096256000000000000 8312584588626588830582315756551168589824 143869806071325678098471452672000000000000))
theorem leaf00070_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9516299883302386716960096256000000000000 8312584588626588830582315756551168589824 143869806071325678098471452672000000000000 raw00070=true := by decide +kernel
#print axioms leaf00070_raw
theorem leaf00070_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00070=true := by decide +kernel
#print axioms leaf00070_rectangular
def affine00070 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00070 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00070_transform : affine00070=(NestedInteger.clearedAll 3 raw00070 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00070_transform
theorem leaf00070_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00070=true := by decide +kernel
#print axioms leaf00070_sign
theorem leaf00070_log : RationalLog.accepts (1773385201/2147483648) (-411042359/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00070_log
def leaf00070 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (28889260421/500000000000) (1773385201/2147483648) (-411042359/4294967296) 1 8 ![52,0,4] ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)] affine00070
theorem leaf00070_checked : FastNestedCellData.accepts 1 0 4 leaf00070=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (28889260421/500000000000) (1773385201/2147483648) (-411042359/4294967296) 1 8 ![52,0,4] ![(3/400),0,(1/4)] ![(1/3200),1,(1/4)] 9516299883302386716960096256000000000000 8312584588626588830582315756551168589824 143869806071325678098471452672000000000000 raw00070 affine00070
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00070_raw leaf00070_rectangular
    leaf00070_transform leaf00070_sign leaf00070_log
#print axioms leaf00070_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
