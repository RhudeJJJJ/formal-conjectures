/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00810 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 84497336469411876885892169728000000000000 6064105101707106353484463679543942578176 6895125801278088560840278016000000000000))
theorem leaf00810_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 84497336469411876885892169728000000000000 6064105101707106353484463679543942578176 6895125801278088560840278016000000000000 raw00810=true := by decide +kernel
#print axioms leaf00810_raw
theorem leaf00810_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00810=true := by decide +kernel
#print axioms leaf00810_rectangular
def affine00810 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00810 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/1600),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00810_transform : affine00810=(NestedInteger.clearedAll 3 raw00810 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/1600),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00810_transform
theorem leaf00810_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00810=true := by decide +kernel
#print axioms leaf00810_sign
theorem leaf00810_log : RationalLog.accepts (41000253/1073741824) (-3506117851/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00810_log
def leaf00810 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (439738539693/500000000000) (41000253/1073741824) (-3506117851/2147483648) 5 8 ![60,0,4] ![(71/1600),0,0] ![(3/3200),1,(1/16)] affine00810
theorem leaf00810_checked : FastNestedCellData.accepts 1 2 4 leaf00810=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (439738539693/500000000000) (41000253/1073741824) (-3506117851/2147483648) 5 8 ![60,0,4] ![(71/1600),0,0] ![(3/3200),1,(1/16)] 84497336469411876885892169728000000000000 6064105101707106353484463679543942578176 6895125801278088560840278016000000000000 raw00810 affine00810
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00810_raw leaf00810_rectangular
    leaf00810_transform leaf00810_sign leaf00810_log
#print axioms leaf00810_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
