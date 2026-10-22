/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01040 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1400505663389363040836921589760000000000 1132149408251271704640504333394692276224 2330014496410356565258797056000000000000))
theorem leaf01040_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1400505663389363040836921589760000000000 1132149408251271704640504333394692276224 2330014496410356565258797056000000000000 raw01040=true := by decide +kernel
#print axioms leaf01040_raw
theorem leaf01040_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01040=true := by decide +kernel
#print axioms leaf01040_rectangular
def affine01040 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01040 (IntegerComputedClassCell.leftNumerator ![(19/80),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/80),0,0] ![(3/160),1,(1/16)]))
theorem leaf01040_transform : affine01040=(NestedInteger.clearedAll 3 raw01040 (IntegerComputedClassCell.leftNumerator ![(19/80),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/80),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01040_transform
theorem leaf01040_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01040=true := by decide +kernel
#print axioms leaf01040_sign
theorem leaf01040_log : RationalLog.accepts (1168314425/2147483648) (-1307247877/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01040_log
def leaf01040 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (60737251313/125000000000) (1168314425/2147483648) (-1307247877/4294967296) 1 8 ![60,0,4] ![(19/80),0,0] ![(3/160),1,(1/16)] affine01040
theorem leaf01040_checked : FastNestedCellData.accepts 1 2 4 leaf01040=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (60737251313/125000000000) (1168314425/2147483648) (-1307247877/4294967296) 1 8 ![60,0,4] ![(19/80),0,0] ![(3/160),1,(1/16)] 1400505663389363040836921589760000000000 1132149408251271704640504333394692276224 2330014496410356565258797056000000000000 raw01040 affine01040
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01040_raw leaf01040_rectangular
    leaf01040_transform leaf01040_sign leaf01040_log
#print axioms leaf01040_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
