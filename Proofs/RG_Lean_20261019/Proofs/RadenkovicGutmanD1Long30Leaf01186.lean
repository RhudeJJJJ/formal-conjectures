/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01186 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1863885705792010002867683328000000000000 2238055433562899779722255069243770929152 86522950074091150939021901824000000000000))
theorem leaf01186_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1863885705792010002867683328000000000000 2238055433562899779722255069243770929152 86522950074091150939021901824000000000000 raw01186=true := by decide +kernel
#print axioms leaf01186_raw
theorem leaf01186_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01186=true := by decide +kernel
#print axioms leaf01186_rectangular
def affine01186 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01186 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01186_transform : affine01186=(NestedInteger.clearedAll 3 raw01186 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01186_transform
theorem leaf01186_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01186=true := by decide +kernel
#print axioms leaf01186_sign
theorem leaf01186_log : RationalLog.accepts (314195923/268435456) (42253419/536870912) 0 8=true := by decide +kernel
#print axioms leaf01186_log
def leaf01186 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (25866610323/1000000000000) (314195923/268435456) (42253419/536870912) 0 8 ![60,0,4] ![(7/16),0,(1/2)] ![(1/32),1,(1/4)] affine01186
theorem leaf01186_checked : FastNestedCellData.accepts 1 2 4 leaf01186=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (25866610323/1000000000000) (314195923/268435456) (42253419/536870912) 0 8 ![60,0,4] ![(7/16),0,(1/2)] ![(1/32),1,(1/4)] 1863885705792010002867683328000000000000 2238055433562899779722255069243770929152 86522950074091150939021901824000000000000 raw01186 affine01186
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01186_raw leaf01186_rectangular
    leaf01186_transform leaf01186_sign leaf01186_log
#print axioms leaf01186_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
