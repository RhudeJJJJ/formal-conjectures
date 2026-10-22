/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00784 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 159218500574262557366632316928000000000000 120029269436155686185836565414019474653184 869147275072146188873632841728000000000000))
theorem leaf00784_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 159218500574262557366632316928000000000000 120029269436155686185836565414019474653184 869147275072146188873632841728000000000000 raw00784=true := by decide +kernel
#print axioms leaf00784_raw
theorem leaf00784_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00784=true := by decide +kernel
#print axioms leaf00784_rectangular
def affine00784 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00784 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00784_transform : affine00784=(NestedInteger.clearedAll 3 raw00784 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00784_transform
theorem leaf00784_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00784=true := by decide +kernel
#print axioms leaf00784_sign
theorem leaf00784_log : RationalLog.accepts (1422469823/2147483648) (-442276517/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00784_log
def leaf00784 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (69050017689/500000000000) (1422469823/2147483648) (-442276517/2147483648) 1 8 ![60,0,4] ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)] affine00784
theorem leaf00784_checked : FastNestedCellData.accepts 1 2 4 leaf00784=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (69050017689/500000000000) (1422469823/2147483648) (-442276517/2147483648) 1 8 ![60,0,4] ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)] 159218500574262557366632316928000000000000 120029269436155686185836565414019474653184 869147275072146188873632841728000000000000 raw00784 affine00784
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00784_raw leaf00784_rectangular
    leaf00784_transform leaf00784_sign leaf00784_log
#print axioms leaf00784_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
