/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00581 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1765006799815820118681808640409600000000000 630850404276892774613162246252305720541184 1318650552247888345339713814528000000000000))
theorem leaf00581_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1765006799815820118681808640409600000000000 630850404276892774613162246252305720541184 1318650552247888345339713814528000000000000 raw00581=true := by decide +kernel
#print axioms leaf00581_raw
theorem leaf00581_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00581=true := by decide +kernel
#print axioms leaf00581_rectangular
def affine00581 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00581 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00581_transform : affine00581=(NestedInteger.clearedAll 3 raw00581 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00581_transform
theorem leaf00581_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00581=true := by decide +kernel
#print axioms leaf00581_sign
theorem leaf00581_log : RationalLog.accepts (1038355655/4294967296) (-1524504687/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00581_log
def leaf00581 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (478406051703/1000000000000) (1038355655/4294967296) (-1524504687/2147483648) 3 8 ![60,0,4] ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00581
theorem leaf00581_checked : FastNestedCellData.accepts 1 2 4 leaf00581=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (478406051703/1000000000000) (1038355655/4294967296) (-1524504687/2147483648) 3 8 ![60,0,4] ![(59/3200),0,(1/16)] ![(1/3200),1,(1/16)] 1765006799815820118681808640409600000000000 630850404276892774613162246252305720541184 1318650552247888345339713814528000000000000 raw00581 affine00581
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00581_raw leaf00581_rectangular
    leaf00581_transform leaf00581_sign leaf00581_log
#print axioms leaf00581_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
