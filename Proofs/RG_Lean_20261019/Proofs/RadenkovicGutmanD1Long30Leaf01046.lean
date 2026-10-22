/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01046 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 102289574129203974890706488524800000000000 88024160995761613193537684537585373806592 198426768321082609386502750208000000000000))
theorem leaf01046_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 102289574129203974890706488524800000000000 88024160995761613193537684537585373806592 198426768321082609386502750208000000000000 raw01046=true := by decide +kernel
#print axioms leaf01046_raw
theorem leaf01046_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01046=true := by decide +kernel
#print axioms leaf01046_rectangular
def affine01046 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01046 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01046_transform : affine01046=(NestedInteger.clearedAll 3 raw01046 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01046_transform
theorem leaf01046_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01046=true := by decide +kernel
#print axioms leaf01046_sign
theorem leaf01046_log : RationalLog.accepts (1280119205/2147483648) (-1110986867/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01046_log
def leaf01046 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (221805156987/500000000000) (1280119205/2147483648) (-1110986867/4294967296) 1 8 ![60,0,4] ![(41/160),0,(1/16)] ![(3/160),1,(1/16)] affine01046
theorem leaf01046_checked : FastNestedCellData.accepts 1 2 4 leaf01046=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (221805156987/500000000000) (1280119205/2147483648) (-1110986867/4294967296) 1 8 ![60,0,4] ![(41/160),0,(1/16)] ![(3/160),1,(1/16)] 102289574129203974890706488524800000000000 88024160995761613193537684537585373806592 198426768321082609386502750208000000000000 raw01046 affine01046
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01046_raw leaf01046_rectangular
    leaf01046_transform leaf01046_sign leaf01046_log
#print axioms leaf01046_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
