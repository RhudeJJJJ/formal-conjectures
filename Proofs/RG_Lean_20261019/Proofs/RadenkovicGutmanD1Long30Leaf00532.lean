/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00532 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 65853314162750933854335270912000000000000 40226852747009147594534089209793619165184 176067082516376979478107127808000000000000))
theorem leaf00532_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 65853314162750933854335270912000000000000 40226852747009147594534089209793619165184 176067082516376979478107127808000000000000 raw00532=true := by decide +kernel
#print axioms leaf00532_raw
theorem leaf00532_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00532=true := by decide +kernel
#print axioms leaf00532_rectangular
def affine00532 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00532 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00532_transform : affine00532=(NestedInteger.clearedAll 3 raw00532 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00532_transform
theorem leaf00532_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00532=true := by decide +kernel
#print axioms leaf00532_sign
theorem leaf00532_log : RationalLog.accepts (533914991/1073741824) (-750189331/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00532_log
def leaf00532 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (114237290049/500000000000) (533914991/1073741824) (-750189331/2147483648) 2 8 ![60,0,4] ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00532
theorem leaf00532_checked : FastNestedCellData.accepts 1 2 4 leaf00532=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (114237290049/500000000000) (533914991/1073741824) (-750189331/2147483648) 2 8 ![60,0,4] ![(49/3200),0,(1/8)] ![(1/3200),1,(1/8)] 65853314162750933854335270912000000000000 40226852747009147594534089209793619165184 176067082516376979478107127808000000000000 raw00532 affine00532
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00532_raw leaf00532_rectangular
    leaf00532_transform leaf00532_sign leaf00532_log
#print axioms leaf00532_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
