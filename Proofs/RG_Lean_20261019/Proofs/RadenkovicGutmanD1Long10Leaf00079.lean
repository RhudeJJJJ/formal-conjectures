/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00079 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3983369792646067769894659686400000000000 3427245518893716329606010567870407245824 52904554230706231659625394995200000000000))
theorem leaf00079_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3983369792646067769894659686400000000000 3427245518893716329606010567870407245824 52904554230706231659625394995200000000000 raw00079=true := by decide +kernel
#print axioms leaf00079_raw
theorem leaf00079_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00079=true := by decide +kernel
#print axioms leaf00079_rectangular
def affine00079 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00079 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00079_transform : affine00079=(NestedInteger.clearedAll 3 raw00079 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00079_transform
theorem leaf00079_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00079=true := by decide +kernel
#print axioms leaf00079_sign
theorem leaf00079_log : RationalLog.accepts (1735257339/2147483648) (-457716925/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00079_log
def leaf00079 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (12956334549/200000000000) (1735257339/2147483648) (-457716925/4294967296) 1 8 ![52,0,4] ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00079
theorem leaf00079_checked : FastNestedCellData.accepts 1 0 4 leaf00079=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (12956334549/200000000000) (1735257339/2147483648) (-457716925/4294967296) 1 8 ![52,0,4] ![(27/3200),0,(1/4)] ![(1/3200),1,(1/4)] 3983369792646067769894659686400000000000 3427245518893716329606010567870407245824 52904554230706231659625394995200000000000 raw00079 affine00079
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00079_raw leaf00079_rectangular
    leaf00079_transform leaf00079_sign leaf00079_log
#print axioms leaf00079_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
