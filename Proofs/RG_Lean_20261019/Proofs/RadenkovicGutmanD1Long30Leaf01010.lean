/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01010 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 154903587070837948508969264742400000000000 87869911398079414924198268827124958756864 139520226569374005224765443276800000000000))
theorem leaf01010_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 154903587070837948508969264742400000000000 87869911398079414924198268827124958756864 139520226569374005224765443276800000000000 raw01010=true := by decide +kernel
#print axioms leaf01010_raw
theorem leaf01010_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01010=true := by decide +kernel
#print axioms leaf01010_rectangular
def affine01010 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01010 (IntegerComputedClassCell.leftNumerator ![(13/80),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/80),0,0] ![(1/80),1,(1/16)]))
theorem leaf01010_transform : affine01010=(NestedInteger.clearedAll 3 raw01010 (IntegerComputedClassCell.leftNumerator ![(13/80),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/80),0,0] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01010_transform
theorem leaf01010_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01010=true := by decide +kernel
#print axioms leaf01010_sign
theorem leaf01010_log : RationalLog.accepts (1494872397/4294967296) (-2266460951/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01010_log
def leaf01010 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (125960104221/200000000000) (1494872397/4294967296) (-2266460951/4294967296) 2 8 ![60,0,4] ![(13/80),0,0] ![(1/80),1,(1/16)] affine01010
theorem leaf01010_checked : FastNestedCellData.accepts 1 2 4 leaf01010=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (125960104221/200000000000) (1494872397/4294967296) (-2266460951/4294967296) 2 8 ![60,0,4] ![(13/80),0,0] ![(1/80),1,(1/16)] 154903587070837948508969264742400000000000 87869911398079414924198268827124958756864 139520226569374005224765443276800000000000 raw01010 affine01010
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01010_raw leaf01010_rectangular
    leaf01010_transform leaf01010_sign leaf01010_log
#print axioms leaf01010_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
