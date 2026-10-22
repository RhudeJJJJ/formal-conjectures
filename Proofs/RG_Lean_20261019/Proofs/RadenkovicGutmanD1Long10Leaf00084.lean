/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00084 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3866220781139454005728589643776000000000000 3519787555200627460668000847065740476416 16793821124068868910382841856000000000000))
theorem leaf00084_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3866220781139454005728589643776000000000000 3519787555200627460668000847065740476416 16793821124068868910382841856000000000000 raw00084=true := by decide +kernel
#print axioms leaf00084_raw
theorem leaf00084_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00084=true := by decide +kernel
#print axioms leaf00084_rectangular
def affine00084 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00084 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00084_transform : affine00084=(NestedInteger.clearedAll 3 raw00084 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00084_transform
theorem leaf00084_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00084=true := by decide +kernel
#print axioms leaf00084_sign
theorem leaf00084_log : RationalLog.accepts (3232601/4294967296) (-7722257057/2147483648) 11 8=true := by decide +kernel
#print axioms leaf00084_log
def leaf00084 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (209588248511/1000000000000) (3232601/4294967296) (-7722257057/2147483648) 11 8 ![52,0,4] ![(29/3200),0,0] ![(1/3200),1,(1/4)] affine00084
theorem leaf00084_checked : FastNestedCellData.accepts 1 0 4 leaf00084=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (209588248511/1000000000000) (3232601/4294967296) (-7722257057/2147483648) 11 8 ![52,0,4] ![(29/3200),0,0] ![(1/3200),1,(1/4)] 3866220781139454005728589643776000000000000 3519787555200627460668000847065740476416 16793821124068868910382841856000000000000 raw00084 affine00084
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00084_raw leaf00084_rectangular
    leaf00084_transform leaf00084_sign leaf00084_log
#print axioms leaf00084_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
