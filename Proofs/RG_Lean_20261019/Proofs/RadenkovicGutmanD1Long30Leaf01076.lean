/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01076 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5884198978025747125681258496000000000000 6151626535230042119739218792472517804032 18833124491707661874131632128000000000000))
theorem leaf01076_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5884198978025747125681258496000000000000 6151626535230042119739218792472517804032 18833124491707661874131632128000000000000 raw01076=true := by decide +kernel
#print axioms leaf01076_raw
theorem leaf01076_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01076=true := by decide +kernel
#print axioms leaf01076_rectangular
def affine01076 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01076 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01076_transform : affine01076=(NestedInteger.clearedAll 3 raw01076 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01076_transform
theorem leaf01076_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01076=true := by decide +kernel
#print axioms leaf01076_sign
theorem leaf01076_log : RationalLog.accepts (1692309639/2147483648) (-63942005/536870912) 1 8=true := by decide +kernel
#print axioms leaf01076_log
def leaf01076 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20414916209/62500000000) (1692309639/2147483648) (-63942005/536870912) 1 8 ![60,0,4] ![(59/160),0,(1/16)] ![(3/160),1,(1/16)] affine01076
theorem leaf01076_checked : FastNestedCellData.accepts 1 2 4 leaf01076=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20414916209/62500000000) (1692309639/2147483648) (-63942005/536870912) 1 8 ![60,0,4] ![(59/160),0,(1/16)] ![(3/160),1,(1/16)] 5884198978025747125681258496000000000000 6151626535230042119739218792472517804032 18833124491707661874131632128000000000000 raw01076 affine01076
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01076_raw leaf01076_rectangular
    leaf01076_transform leaf01076_sign leaf01076_log
#print axioms leaf01076_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
