/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01020 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 106771962251853650500756124467200000000000 70439688117738778530552856073842691407872 121697014078926751245167860121600000000000))
theorem leaf01020_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 106771962251853650500756124467200000000000 70439688117738778530552856073842691407872 121697014078926751245167860121600000000000 raw01020=true := by decide +kernel
#print axioms leaf01020_raw
theorem leaf01020_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01020=true := by decide +kernel
#print axioms leaf01020_rectangular
def affine01020 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01020 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/80),1,(1/16)]))
theorem leaf01020_transform : affine01020=(NestedInteger.clearedAll 3 raw01020 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01020_transform
theorem leaf01020_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01020=true := by decide +kernel
#print axioms leaf01020_sign
theorem leaf01020_log : RationalLog.accepts (1794690863/4294967296) (-1873918257/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01020_log
def leaf01020 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (57881196717/100000000000) (1794690863/4294967296) (-1873918257/4294967296) 2 8 ![60,0,4] ![(3/16),0,0] ![(1/80),1,(1/16)] affine01020
theorem leaf01020_checked : FastNestedCellData.accepts 1 2 4 leaf01020=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (57881196717/100000000000) (1794690863/4294967296) (-1873918257/4294967296) 2 8 ![60,0,4] ![(3/16),0,0] ![(1/80),1,(1/16)] 106771962251853650500756124467200000000000 70439688117738778530552856073842691407872 121697014078926751245167860121600000000000 raw01020 affine01020
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01020_raw leaf01020_rectangular
    leaf01020_transform leaf01020_sign leaf01020_log
#print axioms leaf01020_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
