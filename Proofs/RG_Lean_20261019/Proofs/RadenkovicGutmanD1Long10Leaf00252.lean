/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00252 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 761527199474910448747609587712000000000000 47039285465622020826130713253217281507328 71215583385663030035631570944000000000000))
theorem leaf00252_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 761527199474910448747609587712000000000000 47039285465622020826130713253217281507328 71215583385663030035631570944000000000000 raw00252=true := by decide +kernel
#print axioms leaf00252_raw
theorem leaf00252_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00252=true := by decide +kernel
#print axioms leaf00252_rectangular
def affine00252 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00252 (IntegerComputedClassCell.leftNumerator ![(1/20),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,0] ![(1/640),1,(1/4)]))
theorem leaf00252_transform : affine00252=(NestedInteger.clearedAll 3 raw00252 (IntegerComputedClassCell.leftNumerator ![(1/20),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00252_transform
theorem leaf00252_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00252=true := by decide +kernel
#print axioms leaf00252_sign
theorem leaf00252_log : RationalLog.accepts (79884251/2147483648) (-3534192649/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00252_log
def leaf00252 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (330259777631/500000000000) (79884251/2147483648) (-3534192649/2147483648) 5 8 ![52,0,4] ![(1/20),0,0] ![(1/640),1,(1/4)] affine00252
theorem leaf00252_checked : FastNestedCellData.accepts 1 0 4 leaf00252=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (330259777631/500000000000) (79884251/2147483648) (-3534192649/2147483648) 5 8 ![52,0,4] ![(1/20),0,0] ![(1/640),1,(1/4)] 761527199474910448747609587712000000000000 47039285465622020826130713253217281507328 71215583385663030035631570944000000000000 raw00252 affine00252
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00252_raw leaf00252_rectangular
    leaf00252_transform leaf00252_sign leaf00252_log
#print axioms leaf00252_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
