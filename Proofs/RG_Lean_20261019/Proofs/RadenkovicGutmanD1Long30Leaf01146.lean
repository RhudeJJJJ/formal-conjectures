/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01146 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 114191948627694967035449573376000000000000 146110365233508263391535367241232879190016 1475180905029386677738973167616000000000000))
theorem leaf01146_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 114191948627694967035449573376000000000000 146110365233508263391535367241232879190016 1475180905029386677738973167616000000000000 raw01146=true := by decide +kernel
#print axioms leaf01146_raw
theorem leaf01146_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01146=true := by decide +kernel
#print axioms leaf01146_rectangular
def affine01146 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01146 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01146_transform : affine01146=(NestedInteger.clearedAll 3 raw01146 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01146_transform
theorem leaf01146_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01146=true := by decide +kernel
#print axioms leaf01146_sign
theorem leaf01146_log : RationalLog.accepts (2500113043/2147483648) (326501669/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01146_log
def leaf01146 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (49522863513/500000000000) (2500113043/2147483648) (326501669/4294967296) 0 8 ![60,0,4] ![(15/16),0,(1/2)] ![(1/16),1,(1/4)] affine01146
theorem leaf01146_checked : FastNestedCellData.accepts 1 2 4 leaf01146=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (49522863513/500000000000) (2500113043/2147483648) (326501669/4294967296) 0 8 ![60,0,4] ![(15/16),0,(1/2)] ![(1/16),1,(1/4)] 114191948627694967035449573376000000000000 146110365233508263391535367241232879190016 1475180905029386677738973167616000000000000 raw01146 affine01146
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01146_raw leaf01146_rectangular
    leaf01146_transform leaf01146_sign leaf01146_log
#print axioms leaf01146_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
