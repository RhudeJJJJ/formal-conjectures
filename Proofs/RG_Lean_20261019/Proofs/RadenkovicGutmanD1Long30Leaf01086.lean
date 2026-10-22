/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01086 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 467427939475721381238452256768000000000000 513474495600577794428037448056105118728192 1842176536509157118558301323264000000000000))
theorem leaf01086_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 467427939475721381238452256768000000000000 513474495600577794428037448056105118728192 1842176536509157118558301323264000000000000 raw01086=true := by decide +kernel
#print axioms leaf01086_raw
theorem leaf01086_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01086=true := by decide +kernel
#print axioms leaf01086_rectangular
def affine01086 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01086 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)]))
theorem leaf01086_transform : affine01086=(NestedInteger.clearedAll 3 raw01086 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/16)] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01086_transform
theorem leaf01086_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01086=true := by decide +kernel
#print axioms leaf01086_sign
theorem leaf01086_log : RationalLog.accepts (3689643133/4294967296) (-326233295/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01086_log
def leaf01086 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (278732513103/1000000000000) (3689643133/4294967296) (-326233295/4294967296) 1 8 ![60,0,4] ![(17/40),0,(1/16)] ![(3/80),1,(1/16)] affine01086
theorem leaf01086_checked : FastNestedCellData.accepts 1 2 4 leaf01086=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (278732513103/1000000000000) (3689643133/4294967296) (-326233295/4294967296) 1 8 ![60,0,4] ![(17/40),0,(1/16)] ![(3/80),1,(1/16)] 467427939475721381238452256768000000000000 513474495600577794428037448056105118728192 1842176536509157118558301323264000000000000 raw01086 affine01086
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01086_raw leaf01086_rectangular
    leaf01086_transform leaf01086_sign leaf01086_log
#print axioms leaf01086_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
