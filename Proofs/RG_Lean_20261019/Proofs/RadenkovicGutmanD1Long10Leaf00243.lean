/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00243 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 11612800583768276960559497216000000000000 607610418639600076694499185768081129472 942557838734118427639676928000000000000))
theorem leaf00243_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 11612800583768276960559497216000000000000 607610418639600076694499185768081129472 942557838734118427639676928000000000000 raw00243=true := by decide +kernel
#print axioms leaf00243_raw
theorem leaf00243_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00243=true := by decide +kernel
#print axioms leaf00243_rectangular
def affine00243 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00243 (IntegerComputedClassCell.leftNumerator ![(37/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00243_transform : affine00243=(NestedInteger.clearedAll 3 raw00243 (IntegerComputedClassCell.leftNumerator ![(37/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/800),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00243_transform
theorem leaf00243_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00243=true := by decide +kernel
#print axioms leaf00243_sign
theorem leaf00243_log : RationalLog.accepts (68319909/2147483648) (-7404203437/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00243_log
def leaf00243 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (40289995589/62500000000) (68319909/2147483648) (-7404203437/4294967296) 5 8 ![52,0,4] ![(37/800),0,0] ![(3/3200),1,(1/4)] affine00243
theorem leaf00243_checked : FastNestedCellData.accepts 1 0 4 leaf00243=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (40289995589/62500000000) (68319909/2147483648) (-7404203437/4294967296) 5 8 ![52,0,4] ![(37/800),0,0] ![(3/3200),1,(1/4)] 11612800583768276960559497216000000000000 607610418639600076694499185768081129472 942557838734118427639676928000000000000 raw00243 affine00243
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00243_raw leaf00243_rectangular
    leaf00243_transform leaf00243_sign leaf00243_log
#print axioms leaf00243_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
