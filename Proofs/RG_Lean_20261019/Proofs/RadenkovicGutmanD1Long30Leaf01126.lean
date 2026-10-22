/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01126 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10333513562244351735770382336000000000000 12855935687736102309561243679205193940992 89646932689891268344196104192000000000000))
theorem leaf01126_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10333513562244351735770382336000000000000 12855935687736102309561243679205193940992 89646932689891268344196104192000000000000 raw01126=true := by decide +kernel
#print axioms leaf01126_raw
theorem leaf01126_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01126=true := by decide +kernel
#print axioms leaf01126_rectangular
def affine01126 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01126 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01126_transform : affine01126=(NestedInteger.clearedAll 3 raw01126 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01126_transform
theorem leaf01126_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01126=true := by decide +kernel
#print axioms leaf01126_sign
theorem leaf01126_log : RationalLog.accepts (584150789/536870912) (45312695/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01126_log
def leaf01126 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71703154263/500000000000) (584150789/536870912) (45312695/1073741824) 0 8 ![60,0,4] ![(3/4),0,(1/2)] ![(1/16),1,(1/4)] affine01126
theorem leaf01126_checked : FastNestedCellData.accepts 1 2 4 leaf01126=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71703154263/500000000000) (584150789/536870912) (45312695/1073741824) 0 8 ![60,0,4] ![(3/4),0,(1/2)] ![(1/16),1,(1/4)] 10333513562244351735770382336000000000000 12855935687736102309561243679205193940992 89646932689891268344196104192000000000000 raw01126 affine01126
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01126_raw leaf01126_rectangular
    leaf01126_transform leaf01126_sign leaf01126_log
#print axioms leaf01126_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
