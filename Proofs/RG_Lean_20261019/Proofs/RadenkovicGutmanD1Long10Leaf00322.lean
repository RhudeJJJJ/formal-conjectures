/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00322 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8708978261843725985636885200896000000000000 4598044431754690995466578344770636640944128 9739253712888190608067776217088000000000000))
theorem leaf00322_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8708978261843725985636885200896000000000000 4598044431754690995466578344770636640944128 9739253712888190608067776217088000000000000 raw00322=true := by decide +kernel
#print axioms leaf00322_raw
theorem leaf00322_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00322=true := by decide +kernel
#print axioms leaf00322_rectangular
def affine00322 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00322 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00322_transform : affine00322=(NestedInteger.clearedAll 3 raw00322 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00322_transform
theorem leaf00322_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00322=true := by decide +kernel
#print axioms leaf00322_sign
theorem leaf00322_log : RationalLog.accepts (1540366913/4294967296) (-2202079835/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00322_log
def leaf00322 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (472114657581/1000000000000) (1540366913/4294967296) (-2202079835/4294967296) 2 8 ![52,0,4] ![(33/320),0,(1/4)] ![(1/320),1,(1/4)] affine00322
theorem leaf00322_checked : FastNestedCellData.accepts 1 0 4 leaf00322=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (472114657581/1000000000000) (1540366913/4294967296) (-2202079835/4294967296) 2 8 ![52,0,4] ![(33/320),0,(1/4)] ![(1/320),1,(1/4)] 8708978261843725985636885200896000000000000 4598044431754690995466578344770636640944128 9739253712888190608067776217088000000000000 raw00322 affine00322
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00322_raw leaf00322_rectangular
    leaf00322_transform leaf00322_sign leaf00322_log
#print axioms leaf00322_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
