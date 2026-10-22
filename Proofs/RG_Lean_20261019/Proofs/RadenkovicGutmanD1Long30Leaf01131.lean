/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01131 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 120096060811703326830348153651200000000000 151044907755043094380812077443874998452224 1160024208189026732308919484416000000000000))
theorem leaf01131_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 120096060811703326830348153651200000000000 151044907755043094380812077443874998452224 1160024208189026732308919484416000000000000 raw01131=true := by decide +kernel
#print axioms leaf01131_raw
theorem leaf01131_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01131=true := by decide +kernel
#print axioms leaf01131_rectangular
def affine01131 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01131 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01131_transform : affine01131=(NestedInteger.clearedAll 3 raw01131 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01131_transform
theorem leaf01131_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01131=true := by decide +kernel
#print axioms leaf01131_sign
theorem leaf01131_log : RationalLog.accepts (2389729015/2147483648) (229529959/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01131_log
def leaf01131 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (130208410039/1000000000000) (2389729015/2147483648) (229529959/4294967296) 0 8 ![60,0,4] ![(13/16),0,(1/2)] ![(1/16),1,(1/4)] affine01131
theorem leaf01131_checked : FastNestedCellData.accepts 1 2 4 leaf01131=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (130208410039/1000000000000) (2389729015/2147483648) (229529959/4294967296) 0 8 ![60,0,4] ![(13/16),0,(1/2)] ![(1/16),1,(1/4)] 120096060811703326830348153651200000000000 151044907755043094380812077443874998452224 1160024208189026732308919484416000000000000 raw01131 affine01131
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01131_raw leaf01131_rectangular
    leaf01131_transform leaf01131_sign leaf01131_log
#print axioms leaf01131_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
