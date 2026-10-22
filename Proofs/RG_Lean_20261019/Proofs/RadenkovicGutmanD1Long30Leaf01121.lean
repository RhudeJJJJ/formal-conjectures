/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01121 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 146158345327534978666588851404800000000000 179226282775098154016551635782213056856064 1131013546378622516379720351744000000000000))
theorem leaf01121_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 146158345327534978666588851404800000000000 179226282775098154016551635782213056856064 1131013546378622516379720351744000000000000 raw01121=true := by decide +kernel
#print axioms leaf01121_raw
theorem leaf01121_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01121=true := by decide +kernel
#print axioms leaf01121_rectangular
def affine01121 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01121 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01121_transform : affine01121=(NestedInteger.clearedAll 3 raw01121 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01121_transform
theorem leaf01121_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01121=true := by decide +kernel
#print axioms leaf01121_sign
theorem leaf01121_log : RationalLog.accepts (2273133565/2147483648) (15263923/536870912) 0 8=true := by decide +kernel
#print axioms leaf01121_log
def leaf01121 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (158465195531/1000000000000) (2273133565/2147483648) (15263923/536870912) 0 8 ![60,0,4] ![(11/16),0,(1/2)] ![(1/16),1,(1/4)] affine01121
theorem leaf01121_checked : FastNestedCellData.accepts 1 2 4 leaf01121=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (158465195531/1000000000000) (2273133565/2147483648) (15263923/536870912) 0 8 ![60,0,4] ![(11/16),0,(1/2)] ![(1/16),1,(1/4)] 146158345327534978666588851404800000000000 179226282775098154016551635782213056856064 1131013546378622516379720351744000000000000 raw01121 affine01121
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01121_raw leaf01121_rectangular
    leaf01121_transform leaf01121_sign leaf01121_log
#print axioms leaf01121_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
