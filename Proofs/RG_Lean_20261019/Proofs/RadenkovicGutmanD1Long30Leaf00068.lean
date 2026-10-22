/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00068 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4047820242961812959711461376000000000000 3915105682272619158301023197801226436608 278780260916291597921893220352000000000000))
theorem leaf00068_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4047820242961812959711461376000000000000 3915105682272619158301023197801226436608 278780260916291597921893220352000000000000 raw00068=true := by decide +kernel
#print axioms leaf00068_raw
theorem leaf00068_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00068=true := by decide +kernel
#print axioms leaf00068_rectangular
def affine00068 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00068 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00068_transform : affine00068=(NestedInteger.clearedAll 3 raw00068 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00068_transform
theorem leaf00068_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00068=true := by decide +kernel
#print axioms leaf00068_sign
theorem leaf00068_log : RationalLog.accepts (2048308971/2147483648) (-25384447/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00068_log
def leaf00068 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3510924401/250000000000) (2048308971/2147483648) (-25384447/1073741824) 1 8 ![60,0,4] ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00068
theorem leaf00068_checked : FastNestedCellData.accepts 1 2 4 leaf00068=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3510924401/250000000000) (2048308971/2147483648) (-25384447/1073741824) 1 8 ![60,0,4] ![(29/16000),0,(1/4)] ![(1/16000),1,(1/4)] 4047820242961812959711461376000000000000 3915105682272619158301023197801226436608 278780260916291597921893220352000000000000 raw00068 affine00068
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00068_raw leaf00068_rectangular
    leaf00068_transform leaf00068_sign leaf00068_log
#print axioms leaf00068_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
