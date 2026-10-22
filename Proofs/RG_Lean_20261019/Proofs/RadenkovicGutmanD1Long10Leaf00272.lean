/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00272 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 920886762056685304078797897728000000000000 634995325592397087550476159169832134115328 3179977371225308756000536264704000000000000))
theorem leaf00272_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 920886762056685304078797897728000000000000 634995325592397087550476159169832134115328 3179977371225308756000536264704000000000000 raw00272=true := by decide +kernel
#print axioms leaf00272_raw
theorem leaf00272_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00272=true := by decide +kernel
#print axioms leaf00272_rectangular
def affine00272 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00272 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00272_transform : affine00272=(NestedInteger.clearedAll 3 raw00272 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00272_transform
theorem leaf00272_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00272=true := by decide +kernel
#print axioms leaf00272_sign
theorem leaf00272_log : RationalLog.accepts (1234317139/2147483648) (-594615549/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00272_log
def leaf00272 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (199685485607/1000000000000) (1234317139/2147483648) (-594615549/2147483648) 1 8 ![52,0,4] ![(19/320),0,(1/2)] ![(1/640),1,(1/2)] affine00272
theorem leaf00272_checked : FastNestedCellData.accepts 1 0 4 leaf00272=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (199685485607/1000000000000) (1234317139/2147483648) (-594615549/2147483648) 1 8 ![52,0,4] ![(19/320),0,(1/2)] ![(1/640),1,(1/2)] 920886762056685304078797897728000000000000 634995325592397087550476159169832134115328 3179977371225308756000536264704000000000000 raw00272 affine00272
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00272_raw leaf00272_rectangular
    leaf00272_transform leaf00272_sign leaf00272_log
#print axioms leaf00272_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
