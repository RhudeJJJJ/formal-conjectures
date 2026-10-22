/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00904 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1029469760396484306850214313984000000000000 697041216910551603775039933554179344171008 3122515452086688391744662274048000000000000))
theorem leaf00904_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1029469760396484306850214313984000000000000 697041216910551603775039933554179344171008 3122515452086688391744662274048000000000000 raw00904=true := by decide +kernel
#print axioms leaf00904_raw
theorem leaf00904_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00904=true := by decide +kernel
#print axioms leaf00904_rectangular
def affine00904 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00904 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00904_transform : affine00904=(NestedInteger.clearedAll 3 raw00904 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00904_transform
theorem leaf00904_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00904=true := by decide +kernel
#print axioms leaf00904_sign
theorem leaf00904_log : RationalLog.accepts (2377367737/4294967296) (-317532341/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00904_log
def leaf00904 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (111615335073/500000000000) (2377367737/4294967296) (-317532341/1073741824) 1 8 ![60,0,4] ![(11/160),0,(1/2)] ![(1/640),1,(1/2)] affine00904
theorem leaf00904_checked : FastNestedCellData.accepts 1 2 4 leaf00904=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (111615335073/500000000000) (2377367737/4294967296) (-317532341/1073741824) 1 8 ![60,0,4] ![(11/160),0,(1/2)] ![(1/640),1,(1/2)] 1029469760396484306850214313984000000000000 697041216910551603775039933554179344171008 3122515452086688391744662274048000000000000 raw00904 affine00904
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00904_raw leaf00904_rectangular
    leaf00904_transform leaf00904_sign leaf00904_log
#print axioms leaf00904_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
