/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01090 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 297758889022440308406310928384000000000000 337025862312318205114719521316931104669696 1304963104692582909312598278144000000000000))
theorem leaf01090_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 297758889022440308406310928384000000000000 337025862312318205114719521316931104669696 1304963104692582909312598278144000000000000 raw01090=true := by decide +kernel
#print axioms leaf01090_raw
theorem leaf01090_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01090=true := by decide +kernel
#print axioms leaf01090_rectangular
def affine01090 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01090 (IntegerComputedClassCell.leftNumerator ![(37/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/80),0,0] ![(3/80),1,(1/16)]))
theorem leaf01090_transform : affine01090=(NestedInteger.clearedAll 3 raw01090 (IntegerComputedClassCell.leftNumerator ![(37/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/80),0,0] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01090_transform
theorem leaf01090_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01090=true := by decide +kernel
#print axioms leaf01090_sign
theorem leaf01090_log : RationalLog.accepts (3863548361/4294967296) (-113664089/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01090_log
def leaf01090 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (64566166871/250000000000) (3863548361/4294967296) (-113664089/2147483648) 1 8 ![60,0,4] ![(37/80),0,0] ![(3/80),1,(1/16)] affine01090
theorem leaf01090_checked : FastNestedCellData.accepts 1 2 4 leaf01090=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (64566166871/250000000000) (3863548361/4294967296) (-113664089/2147483648) 1 8 ![60,0,4] ![(37/80),0,0] ![(3/80),1,(1/16)] 297758889022440308406310928384000000000000 337025862312318205114719521316931104669696 1304963104692582909312598278144000000000000 raw01090 affine01090
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01090_raw leaf01090_rectangular
    leaf01090_transform leaf01090_sign leaf01090_log
#print axioms leaf01090_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
