/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00420 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 145244141232437344183854825472000000000000 179046040426138455693697221483184412164096 5684939263516422363182868201472000000000000))
theorem leaf00420_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 145244141232437344183854825472000000000000 179046040426138455693697221483184412164096 5684939263516422363182868201472000000000000 raw00420=true := by decide +kernel
#print axioms leaf00420_raw
theorem leaf00420_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00420=true := by decide +kernel
#print axioms leaf00420_rectangular
def affine00420 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00420 (IntegerComputedClassCell.leftNumerator ![(7/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf00420_transform : affine00420=(NestedInteger.clearedAll 3 raw00420 (IntegerComputedClassCell.leftNumerator ![(7/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00420_transform
theorem leaf00420_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00420=true := by decide +kernel
#print axioms leaf00420_sign
theorem leaf00420_log : RationalLog.accepts (2566427023/2147483648) (191360021/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00420_log
def leaf00420 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (31494802693/1000000000000) (2566427023/2147483648) (191360021/2147483648) 0 8 ![52,0,4] ![(7/16),0,0] ![(1/16),1,(1/2)] affine00420
theorem leaf00420_checked : FastNestedCellData.accepts 1 0 4 leaf00420=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (31494802693/1000000000000) (2566427023/2147483648) (191360021/2147483648) 0 8 ![52,0,4] ![(7/16),0,0] ![(1/16),1,(1/2)] 145244141232437344183854825472000000000000 179046040426138455693697221483184412164096 5684939263516422363182868201472000000000000 raw00420 affine00420
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00420_raw leaf00420_rectangular
    leaf00420_transform leaf00420_sign leaf00420_log
#print axioms leaf00420_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
