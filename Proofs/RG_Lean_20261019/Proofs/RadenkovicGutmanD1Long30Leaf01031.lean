/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01031 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 119179358657370309095527442022400000000000 89148226251482155947116053488050903187456 172481054271110943865923698688000000000000))
theorem leaf01031_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 119179358657370309095527442022400000000000 89148226251482155947116053488050903187456 172481054271110943865923698688000000000000 raw01031=true := by decide +kernel
#print axioms leaf01031_raw
theorem leaf01031_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01031=true := by decide +kernel
#print axioms leaf01031_rectangular
def affine01031 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01031 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)]))
theorem leaf01031_transform : affine01031=(NestedInteger.clearedAll 3 raw01031 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/16)] ![(3/320),1,(1/16)])) := by decide +kernel
#print axioms leaf01031_transform
theorem leaf01031_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01031=true := by decide +kernel
#print axioms leaf01031_sign
theorem leaf01031_log : RationalLog.accepts (529500755/1073741824) (-1518207163/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01031_log
def leaf01031 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (516858078287/1000000000000) (529500755/1073741824) (-1518207163/4294967296) 2 8 ![60,0,4] ![(67/320),0,(1/16)] ![(3/320),1,(1/16)] affine01031
theorem leaf01031_checked : FastNestedCellData.accepts 1 2 4 leaf01031=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (516858078287/1000000000000) (529500755/1073741824) (-1518207163/4294967296) 2 8 ![60,0,4] ![(67/320),0,(1/16)] ![(3/320),1,(1/16)] 119179358657370309095527442022400000000000 89148226251482155947116053488050903187456 172481054271110943865923698688000000000000 raw01031 affine01031
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01031_raw leaf01031_rectangular
    leaf01031_transform leaf01031_sign leaf01031_log
#print axioms leaf01031_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
