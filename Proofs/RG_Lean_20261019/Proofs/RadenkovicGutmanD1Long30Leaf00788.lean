/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00788 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12510564287475035206344874393600000000000 7375034207931084468289534199074041888768 27186097573704152466404356915200000000000))
theorem leaf00788_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12510564287475035206344874393600000000000 7375034207931084468289534199074041888768 27186097573704152466404356915200000000000 raw00788=true := by decide +kernel
#print axioms leaf00788_raw
theorem leaf00788_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00788=true := by decide +kernel
#print axioms leaf00788_rectangular
def affine00788 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00788 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00788_transform : affine00788=(NestedInteger.clearedAll 3 raw00788 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00788_transform
theorem leaf00788_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00788=true := by decide +kernel
#print axioms leaf00788_sign
theorem leaf00788_log : RationalLog.accepts (995808711/2147483648) (-825167253/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00788_log
def leaf00788 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27127961959/100000000000) (995808711/2147483648) (-825167253/2147483648) 2 8 ![60,0,4] ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00788
theorem leaf00788_checked : FastNestedCellData.accepts 1 2 4 leaf00788=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27127961959/100000000000) (995808711/2147483648) (-825167253/2147483648) 2 8 ![60,0,4] ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)] 12510564287475035206344874393600000000000 7375034207931084468289534199074041888768 27186097573704152466404356915200000000000 raw00788 affine00788
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00788_raw leaf00788_rectangular
    leaf00788_transform leaf00788_sign leaf00788_log
#print axioms leaf00788_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
