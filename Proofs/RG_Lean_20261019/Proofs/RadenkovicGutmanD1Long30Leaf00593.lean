/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00593 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 41428656494967991612473344000000000000 30475169279033463997634787876444045312 214382205220376241040785408000000000000))
theorem leaf00593_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 41428656494967991612473344000000000000 30475169279033463997634787876444045312 214382205220376241040785408000000000000 raw00593=true := by decide +kernel
#print axioms leaf00593_raw
theorem leaf00593_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00593=true := by decide +kernel
#print axioms leaf00593_rectangular
def affine00593 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00593 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00593_transform : affine00593=(NestedInteger.clearedAll 3 raw00593 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00593_transform
theorem leaf00593_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00593=true := by decide +kernel
#print axioms leaf00593_sign
theorem leaf00593_log : RationalLog.accepts (691545393/1073741824) (-472420721/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00593_log
def leaf00593 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71076723107/500000000000) (691545393/1073741824) (-472420721/2147483648) 1 8 ![60,0,4] ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00593
theorem leaf00593_checked : FastNestedCellData.accepts 1 2 4 leaf00593=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71076723107/500000000000) (691545393/1073741824) (-472420721/2147483648) 1 8 ![60,0,4] ![(61/3200),0,(1/4)] ![(1/3200),1,(1/4)] 41428656494967991612473344000000000000 30475169279033463997634787876444045312 214382205220376241040785408000000000000 raw00593 affine00593
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00593_raw leaf00593_rectangular
    leaf00593_transform leaf00593_sign leaf00593_log
#print axioms leaf00593_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
