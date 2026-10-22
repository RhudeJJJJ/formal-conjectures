/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00503 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1470400905691151705715612057600000000000 1171062662756019504385563783597523992576 11477680354961978543279439872000000000000))
theorem leaf00503_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1470400905691151705715612057600000000000 1171062662756019504385563783597523992576 11477680354961978543279439872000000000000 raw00503=true := by decide +kernel
#print axioms leaf00503_raw
theorem leaf00503_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00503=true := by decide +kernel
#print axioms leaf00503_rectangular
def affine00503 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00503 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00503_transform : affine00503=(NestedInteger.clearedAll 3 raw00503 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00503_transform
theorem leaf00503_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00503=true := by decide +kernel
#print axioms leaf00503_sign
theorem leaf00503_log : RationalLog.accepts (1551961685/2147483648) (-697453389/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00503_log
def leaf00503 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12753694851/125000000000) (1551961685/2147483648) (-697453389/4294967296) 1 8 ![60,0,4] ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00503
theorem leaf00503_checked : FastNestedCellData.accepts 1 2 4 leaf00503=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12753694851/125000000000) (1551961685/2147483648) (-697453389/4294967296) 1 8 ![60,0,4] ![(43/3200),0,(1/4)] ![(1/3200),1,(1/4)] 1470400905691151705715612057600000000000 1171062662756019504385563783597523992576 11477680354961978543279439872000000000000 raw00503 affine00503
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00503_raw leaf00503_rectangular
    leaf00503_transform leaf00503_sign leaf00503_log
#print axioms leaf00503_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
