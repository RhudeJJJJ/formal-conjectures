/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00967 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 137508720078213334078561294745600000000000 63763175989909895885150811281474514321408 106922581722794363141316673536000000000000))
theorem leaf00967_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 137508720078213334078561294745600000000000 63763175989909895885150811281474514321408 106922581722794363141316673536000000000000 raw00967=true := by decide +kernel
#print axioms leaf00967_raw
theorem leaf00967_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00967=true := by decide +kernel
#print axioms leaf00967_rectangular
def affine00967 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00967 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00967_transform : affine00967=(NestedInteger.clearedAll 3 raw00967 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00967_transform
theorem leaf00967_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00967=true := by decide +kernel
#print axioms leaf00967_sign
theorem leaf00967_log : RationalLog.accepts (623794755/2147483648) (-2654785163/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00967_log
def leaf00967 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (298174506089/500000000000) (623794755/2147483648) (-2654785163/4294967296) 2 8 ![60,0,4] ![(17/160),0,(1/8)] ![(1/160),1,(1/8)] affine00967
theorem leaf00967_checked : FastNestedCellData.accepts 1 2 4 leaf00967=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (298174506089/500000000000) (623794755/2147483648) (-2654785163/4294967296) 2 8 ![60,0,4] ![(17/160),0,(1/8)] ![(1/160),1,(1/8)] 137508720078213334078561294745600000000000 63763175989909895885150811281474514321408 106922581722794363141316673536000000000000 raw00967 affine00967
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00967_raw leaf00967_rectangular
    leaf00967_transform leaf00967_sign leaf00967_log
#print axioms leaf00967_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
