/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01030 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9975957908906152054595170336768000000000000 7309647680537660894864461270493976227479552 13516416294367441861287004340224000000000000))
theorem leaf01030_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9975957908906152054595170336768000000000000 7309647680537660894864461270493976227479552 13516416294367441861287004340224000000000000 raw01030=true := by decide +kernel
#print axioms leaf01030_raw
theorem leaf01030_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01030=true := by decide +kernel
#print axioms leaf01030_rectangular
def affine01030 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01030 (IntegerComputedClassCell.leftNumerator ![(67/320),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/320),0,0] ![(3/320),1,(1/16)]))
theorem leaf01030_transform : affine01030=(NestedInteger.clearedAll 3 raw01030 (IntegerComputedClassCell.leftNumerator ![(67/320),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,0] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/320),0,0] ![(3/320),1,(1/16)])) := by decide +kernel
#print axioms leaf01030_transform
theorem leaf01030_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01030=true := by decide +kernel
#print axioms leaf01030_sign
theorem leaf01030_log : RationalLog.accepts (2042471753/4294967296) (-1596188639/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01030_log
def leaf01030 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (540797761873/1000000000000) (2042471753/4294967296) (-1596188639/4294967296) 2 8 ![60,0,4] ![(67/320),0,0] ![(3/320),1,(1/16)] affine01030
theorem leaf01030_checked : FastNestedCellData.accepts 1 2 4 leaf01030=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (540797761873/1000000000000) (2042471753/4294967296) (-1596188639/4294967296) 2 8 ![60,0,4] ![(67/320),0,0] ![(3/320),1,(1/16)] 9975957908906152054595170336768000000000000 7309647680537660894864461270493976227479552 13516416294367441861287004340224000000000000 raw01030 affine01030
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01030_raw leaf01030_rectangular
    leaf01030_transform leaf01030_sign leaf01030_log
#print axioms leaf01030_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
