/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00982 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2692069580638128699435592450048000000000000 1389424415173789496811156845506525340368896 2380172189902966425968556638208000000000000))
theorem leaf00982_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2692069580638128699435592450048000000000000 1389424415173789496811156845506525340368896 2380172189902966425968556638208000000000000 raw00982=true := by decide +kernel
#print axioms leaf00982_raw
theorem leaf00982_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00982=true := by decide +kernel
#print axioms leaf00982_rectangular
def affine00982 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00982 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00982_transform : affine00982=(NestedInteger.clearedAll 3 raw00982 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00982_transform
theorem leaf00982_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00982=true := by decide +kernel
#print axioms leaf00982_sign
theorem leaf00982_log : RationalLog.accepts (1399658241/4294967296) (-1203896385/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00982_log
def leaf00982 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (291874768781/500000000000) (1399658241/4294967296) (-1203896385/2147483648) 2 8 ![60,0,4] ![(1/8),0,(1/8)] ![(1/160),1,(1/8)] affine00982
theorem leaf00982_checked : FastNestedCellData.accepts 1 2 4 leaf00982=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (291874768781/500000000000) (1399658241/4294967296) (-1203896385/2147483648) 2 8 ![60,0,4] ![(1/8),0,(1/8)] ![(1/160),1,(1/8)] 2692069580638128699435592450048000000000000 1389424415173789496811156845506525340368896 2380172189902966425968556638208000000000000 raw00982 affine00982
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00982_raw leaf00982_rectangular
    leaf00982_transform leaf00982_sign leaf00982_log
#print axioms leaf00982_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
