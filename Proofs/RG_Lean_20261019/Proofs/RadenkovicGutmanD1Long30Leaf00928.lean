/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00928 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15502067516678685905057931591680000000000 8187383507851650666937011826112535199744 19485216154574976155307841945600000000000))
theorem leaf00928_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15502067516678685905057931591680000000000 8187383507851650666937011826112535199744 19485216154574976155307841945600000000000 raw00928=true := by decide +kernel
#print axioms leaf00928_raw
theorem leaf00928_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00928=true := by decide +kernel
#print axioms leaf00928_rectangular
def affine00928 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00928 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00928_transform : affine00928=(NestedInteger.clearedAll 3 raw00928 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00928_transform
theorem leaf00928_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00928=true := by decide +kernel
#print axioms leaf00928_sign
theorem leaf00928_log : RationalLog.accepts (1597241695/4294967296) (-2124217323/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00928_log
def leaf00928 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42018438199/100000000000) (1597241695/4294967296) (-2124217323/4294967296) 2 8 ![60,0,4] ![(13/160),0,(1/4)] ![(1/320),1,(1/4)] affine00928
theorem leaf00928_checked : FastNestedCellData.accepts 1 2 4 leaf00928=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42018438199/100000000000) (1597241695/4294967296) (-2124217323/4294967296) 2 8 ![60,0,4] ![(13/160),0,(1/4)] ![(1/320),1,(1/4)] 15502067516678685905057931591680000000000 8187383507851650666937011826112535199744 19485216154574976155307841945600000000000 raw00928 affine00928
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00928_raw leaf00928_rectangular
    leaf00928_transform leaf00928_sign leaf00928_log
#print axioms leaf00928_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
