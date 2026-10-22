/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01192 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 408911251675182748292964417536000000000000 484842716186758005981541392822066430869504 21872153101337923075771805466624000000000000))
theorem leaf01192_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 408911251675182748292964417536000000000000 484842716186758005981541392822066430869504 21872153101337923075771805466624000000000000 raw01192=true := by decide +kernel
#print axioms leaf01192_raw
theorem leaf01192_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01192=true := by decide +kernel
#print axioms leaf01192_rectangular
def affine01192 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01192 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01192_transform : affine01192=(NestedInteger.clearedAll 3 raw01192 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/32),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01192_transform
theorem leaf01192_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01192=true := by decide +kernel
#print axioms leaf01192_sign
theorem leaf01192_log : RationalLog.accepts (4982069339/4294967296) (159344783/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01192_log
def leaf01192 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (22167123371/1000000000000) (4982069339/4294967296) (159344783/2147483648) 0 8 ![60,0,4] ![(13/32),0,(3/4)] ![(1/32),1,(1/8)] affine01192
theorem leaf01192_checked : FastNestedCellData.accepts 1 2 4 leaf01192=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (22167123371/1000000000000) (4982069339/4294967296) (159344783/2147483648) 0 8 ![60,0,4] ![(13/32),0,(3/4)] ![(1/32),1,(1/8)] 408911251675182748292964417536000000000000 484842716186758005981541392822066430869504 21872153101337923075771805466624000000000000 raw01192 affine01192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01192_raw leaf01192_rectangular
    leaf01192_transform leaf01192_sign leaf01192_log
#print axioms leaf01192_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
