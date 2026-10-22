/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01033 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 315577176743366532768338647449600000000000 243146542618442768832093651463927668670464 568515390165522389789465745817600000000000))
theorem leaf01033_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 315577176743366532768338647449600000000000 243146542618442768832093651463927668670464 568515390165522389789465745817600000000000 raw01033=true := by decide +kernel
#print axioms leaf01033_raw
theorem leaf01033_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01033=true := by decide +kernel
#print axioms leaf01033_rectangular
def affine01033 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01033 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)]))
theorem leaf01033_transform : affine01033=(NestedInteger.clearedAll 3 raw01033 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/4)] ![(3/320),1,(1/4)])) := by decide +kernel
#print axioms leaf01033_transform
theorem leaf01033_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01033=true := by decide +kernel
#print axioms leaf01033_sign
theorem leaf01033_log : RationalLog.accepts (2317871851/4294967296) (-331139025/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01033_log
def leaf01033 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (85537365153/200000000000) (2317871851/4294967296) (-331139025/1073741824) 1 8 ![60,0,4] ![(67/320),0,(1/4)] ![(3/320),1,(1/4)] affine01033
theorem leaf01033_checked : FastNestedCellData.accepts 1 2 4 leaf01033=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (85537365153/200000000000) (2317871851/4294967296) (-331139025/1073741824) 1 8 ![60,0,4] ![(67/320),0,(1/4)] ![(3/320),1,(1/4)] 315577176743366532768338647449600000000000 243146542618442768832093651463927668670464 568515390165522389789465745817600000000000 raw01033 affine01033
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01033_raw leaf01033_rectangular
    leaf01033_transform leaf01033_sign leaf01033_log
#print axioms leaf01033_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
