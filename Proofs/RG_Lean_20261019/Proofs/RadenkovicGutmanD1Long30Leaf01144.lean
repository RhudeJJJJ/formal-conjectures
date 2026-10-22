/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01144 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4976536826273641983483104460800000000000 6338387099573750749848527972933572755456 58736933307036882312293567692800000000000))
theorem leaf01144_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4976536826273641983483104460800000000000 6338387099573750749848527972933572755456 58736933307036882312293567692800000000000 raw01144=true := by decide +kernel
#print axioms leaf01144_raw
theorem leaf01144_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01144=true := by decide +kernel
#print axioms leaf01144_rectangular
def affine01144 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01144 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01144_transform : affine01144=(NestedInteger.clearedAll 3 raw01144 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01144_transform
theorem leaf01144_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01144=true := by decide +kernel
#print axioms leaf01144_sign
theorem leaf01144_log : RationalLog.accepts (2468745693/2147483648) (74847023/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01144_log
def leaf01144 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10791144077/100000000000) (2468745693/2147483648) (74847023/1073741824) 0 8 ![60,0,4] ![(15/16),0,(15/16)] ![(1/16),1,(1/16)] affine01144
theorem leaf01144_checked : FastNestedCellData.accepts 1 2 4 leaf01144=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10791144077/100000000000) (2468745693/2147483648) (74847023/1073741824) 0 8 ![60,0,4] ![(15/16),0,(15/16)] ![(1/16),1,(1/16)] 4976536826273641983483104460800000000000 6338387099573750749848527972933572755456 58736933307036882312293567692800000000000 raw01144 affine01144
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01144_raw leaf01144_rectangular
    leaf01144_transform leaf01144_sign leaf01144_log
#print axioms leaf01144_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
