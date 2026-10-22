/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01085 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5073901954989556231154171904000000000000 5583159926186776110437480345508331388928 19822469717530366560843071488000000000000))
theorem leaf01085_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5073901954989556231154171904000000000000 5583159926186776110437480345508331388928 19822469717530366560843071488000000000000 raw01085=true := by decide +kernel
#print axioms leaf01085_raw
theorem leaf01085_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01085=true := by decide +kernel
#print axioms leaf01085_rectangular
def affine01085 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01085 (IntegerComputedClassCell.leftNumerator ![(17/40),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/40),0,0] ![(3/80),1,(1/16)]))
theorem leaf01085_transform : affine01085=(NestedInteger.clearedAll 3 raw01085 (IntegerComputedClassCell.leftNumerator ![(17/40),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/40),0,0] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01085_transform
theorem leaf01085_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01085=true := by decide +kernel
#print axioms leaf01085_sign
theorem leaf01085_log : RationalLog.accepts (460930739/536870912) (-327512525/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01085_log
def leaf01085 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (70414534689/250000000000) (460930739/536870912) (-327512525/4294967296) 1 8 ![60,0,4] ![(17/40),0,0] ![(3/80),1,(1/16)] affine01085
theorem leaf01085_checked : FastNestedCellData.accepts 1 2 4 leaf01085=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (70414534689/250000000000) (460930739/536870912) (-327512525/4294967296) 1 8 ![60,0,4] ![(17/40),0,0] ![(3/80),1,(1/16)] 5073901954989556231154171904000000000000 5583159926186776110437480345508331388928 19822469717530366560843071488000000000000 raw01085 affine01085
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01085_raw leaf01085_rectangular
    leaf01085_transform leaf01085_sign leaf01085_log
#print axioms leaf01085_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
