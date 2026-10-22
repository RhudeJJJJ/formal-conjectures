/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01008 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2120309970625644630963751223296000000000000 1380908647804662136419392307434572256116736 3003484015088188626550038462464000000000000))
theorem leaf01008_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2120309970625644630963751223296000000000000 1380908647804662136419392307434572256116736 3003484015088188626550038462464000000000000 raw01008=true := by decide +kernel
#print axioms leaf01008_raw
theorem leaf01008_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01008=true := by decide +kernel
#print axioms leaf01008_rectangular
def affine01008 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01008 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf01008_transform : affine01008=(NestedInteger.clearedAll 3 raw01008 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01008_transform
theorem leaf01008_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01008=true := by decide +kernel
#print axioms leaf01008_sign
theorem leaf01008_log : RationalLog.accepts (958101107/2147483648) (-866615695/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01008_log
def leaf01008 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (459768935299/1000000000000) (958101107/2147483648) (-866615695/2147483648) 2 8 ![60,0,4] ![(5/32),0,(1/4)] ![(1/160),1,(1/4)] affine01008
theorem leaf01008_checked : FastNestedCellData.accepts 1 2 4 leaf01008=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (459768935299/1000000000000) (958101107/2147483648) (-866615695/2147483648) 2 8 ![60,0,4] ![(5/32),0,(1/4)] ![(1/160),1,(1/4)] 2120309970625644630963751223296000000000000 1380908647804662136419392307434572256116736 3003484015088188626550038462464000000000000 raw01008 affine01008
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01008_raw leaf01008_rectangular
    leaf01008_transform leaf01008_sign leaf01008_log
#print axioms leaf01008_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
