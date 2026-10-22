/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00989 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 298110844233086320822396859187200000000000 203430715201489568547331209887568879419392 629402521352002702008635097088000000000000))
theorem leaf00989_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 298110844233086320822396859187200000000000 203430715201489568547331209887568879419392 629402521352002702008635097088000000000000 raw00989=true := by decide +kernel
#print axioms leaf00989_raw
theorem leaf00989_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00989=true := by decide +kernel
#print axioms leaf00989_rectangular
def affine00989 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00989 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00989_transform : affine00989=(NestedInteger.clearedAll 3 raw00989 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00989_transform
theorem leaf00989_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00989=true := by decide +kernel
#print axioms leaf00989_sign
theorem leaf00989_log : RationalLog.accepts (1107488045/2147483648) (-355517179/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00989_log
def leaf00989 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (323212424959/1000000000000) (1107488045/2147483648) (-355517179/1073741824) 1 8 ![60,0,4] ![(21/160),0,(1/2)] ![(1/160),1,(1/2)] affine00989
theorem leaf00989_checked : FastNestedCellData.accepts 1 2 4 leaf00989=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (323212424959/1000000000000) (1107488045/2147483648) (-355517179/1073741824) 1 8 ![60,0,4] ![(21/160),0,(1/2)] ![(1/160),1,(1/2)] 298110844233086320822396859187200000000000 203430715201489568547331209887568879419392 629402521352002702008635097088000000000000 raw00989 affine00989
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00989_raw leaf00989_rectangular
    leaf00989_transform leaf00989_sign leaf00989_log
#print axioms leaf00989_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
