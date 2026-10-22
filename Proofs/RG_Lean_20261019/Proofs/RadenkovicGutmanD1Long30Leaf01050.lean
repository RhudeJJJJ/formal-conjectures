/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01050 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6229576747953967266981845401600000000000 5583008578831451879827945476338931990528 12915746348765538366863179776000000000000))
theorem leaf01050_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6229576747953967266981845401600000000000 5583008578831451879827945476338931990528 12915746348765538366863179776000000000000 raw01050=true := by decide +kernel
#print axioms leaf01050_raw
theorem leaf01050_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01050=true := by decide +kernel
#print axioms leaf01050_rectangular
def affine01050 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01050 (IntegerComputedClassCell.leftNumerator ![(11/40),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/40),0,0] ![(3/160),1,(1/16)]))
theorem leaf01050_transform : affine01050=(NestedInteger.clearedAll 3 raw01050 (IntegerComputedClassCell.leftNumerator ![(11/40),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/40),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01050_transform
theorem leaf01050_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01050=true := by decide +kernel
#print axioms leaf01050_sign
theorem leaf01050_log : RationalLog.accepts (167968035/268435456) (-503409703/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01050_log
def leaf01050 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (432263721203/1000000000000) (167968035/268435456) (-503409703/2147483648) 1 8 ![60,0,4] ![(11/40),0,0] ![(3/160),1,(1/16)] affine01050
theorem leaf01050_checked : FastNestedCellData.accepts 1 2 4 leaf01050=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (432263721203/1000000000000) (167968035/268435456) (-503409703/2147483648) 1 8 ![60,0,4] ![(11/40),0,0] ![(3/160),1,(1/16)] 6229576747953967266981845401600000000000 5583008578831451879827945476338931990528 12915746348765538366863179776000000000000 raw01050 affine01050
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01050_raw leaf01050_rectangular
    leaf01050_transform leaf01050_sign leaf01050_log
#print axioms leaf01050_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
