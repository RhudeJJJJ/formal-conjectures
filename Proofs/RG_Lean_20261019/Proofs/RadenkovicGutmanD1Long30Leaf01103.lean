/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01103 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3822063532044253466164730003456000000000000 4420758946752995195645437566432781025673216 21336277698842314568741186174976000000000000))
theorem leaf01103_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3822063532044253466164730003456000000000000 4420758946752995195645437566432781025673216 21336277698842314568741186174976000000000000 raw01103=true := by decide +kernel
#print axioms leaf01103_raw
theorem leaf01103_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01103=true := by decide +kernel
#print axioms leaf01103_rectangular
def affine01103 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01103 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01103_transform : affine01103=(NestedInteger.clearedAll 3 raw01103 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/32),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01103_transform
theorem leaf01103_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01103=true := by decide +kernel
#print axioms leaf01103_sign
theorem leaf01103_log : RationalLog.accepts (4115110991/4294967296) (-45932691/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01103_log
def leaf01103 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (207194479241/1000000000000) (4115110991/4294967296) (-45932691/2147483648) 1 8 ![60,0,4] ![(17/32),0,(7/8)] ![(1/32),1,(1/16)] affine01103
theorem leaf01103_checked : FastNestedCellData.accepts 1 2 4 leaf01103=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (207194479241/1000000000000) (4115110991/4294967296) (-45932691/2147483648) 1 8 ![60,0,4] ![(17/32),0,(7/8)] ![(1/32),1,(1/16)] 3822063532044253466164730003456000000000000 4420758946752995195645437566432781025673216 21336277698842314568741186174976000000000000 raw01103 affine01103
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01103_raw leaf01103_rectangular
    leaf01103_transform leaf01103_sign leaf01103_log
#print axioms leaf01103_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
