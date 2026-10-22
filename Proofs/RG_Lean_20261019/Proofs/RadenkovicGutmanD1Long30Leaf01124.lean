/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01124 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11276924408937637875801915392000000000000 13784225083817770456587970213147928690688 88078811136655980584924872704000000000000))
theorem leaf01124_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11276924408937637875801915392000000000000 13784225083817770456587970213147928690688 88078811136655980584924872704000000000000 raw01124=true := by decide +kernel
#print axioms leaf01124_raw
theorem leaf01124_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01124=true := by decide +kernel
#print axioms leaf01124_rectangular
def affine01124 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01124 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01124_transform : affine01124=(NestedInteger.clearedAll 3 raw01124 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/16),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01124_transform
theorem leaf01124_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01124=true := by decide +kernel
#print axioms leaf01124_sign
theorem leaf01124_log : RationalLog.accepts (2269741401/2147483648) (29726083/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01124_log
def leaf01124 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19562345509/125000000000) (2269741401/2147483648) (29726083/1073741824) 0 8 ![60,0,4] ![(11/16),0,(15/16)] ![(1/16),1,(1/16)] affine01124
theorem leaf01124_checked : FastNestedCellData.accepts 1 2 4 leaf01124=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19562345509/125000000000) (2269741401/2147483648) (29726083/1073741824) 0 8 ![60,0,4] ![(11/16),0,(15/16)] ![(1/16),1,(1/16)] 11276924408937637875801915392000000000000 13784225083817770456587970213147928690688 88078811136655980584924872704000000000000 raw01124 affine01124
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01124_raw leaf01124_rectangular
    leaf01124_transform leaf01124_sign leaf01124_log
#print axioms leaf01124_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
